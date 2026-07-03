import Mathlib
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.Sylow
import Mathlib.LinearAlgebra.TensorPower.Basic
import Mathlib.NumberTheory.Niven
import Mathlib.RepresentationTheory.Maschke
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Remark_8_8_1_2 (from Chap08) -/
open scoped MonoidAlgebra

universe u v

namespace Representation

noncomputable section

section

variable {G : Type u} [Group G]
variable {V : Type v} [AddCommGroup V] [Module ℂ V]
variable (ρ : Representation ℂ G V) (A : Subgroup G) [Finite A] [IsMulCommutative A]

-- Source/core/bridge triage:
-- * source-facing: the left side is exactly condition `(b)` from Proposition `8-8.1-1`, namely
--   that the restricted `MonoidAlgebra ℂ A`-module is isotypic. The semisimplicity input is only
--   the finiteness of the restricted action on `A`, so the ambient hypothesis should be `[Finite
--   A]`, not `[Finite G]`.
-- * core/canonical: the owner is `IsIsotypic` on the carrier `V` endowed with the restricted
--   `MonoidAlgebra ℂ A`-module structure coming from `ρ.comp A.subtype`.
-- * bridge/view: the scalar-action side should be expressed by the canonical degree-`1`
--   character `χ : A →* ℂˣ`, with the pointwise “every `a` acts by a homothety” wording kept only
--   as an informal reformulation.
--
-- Primitive data are only the restricted representation `ρ.comp A.subtype`; naming a specific
-- irreducible type belongs to the derived companion predicate `IsIsotypicOfType`, not to the main
-- remark surface. The scalar side is also intrinsic at the level of a single linear character,
-- not as unrelated elementwise witnesses. Proof sketch: because `A` is finite, Maschke makes the
-- restricted `MonoidAlgebra ℂ A`-module semisimple. If it is isotypic, then any irreducible
-- constituent is one-dimensional because `A` is commutative, so every `a : A` acts by a scalar on
-- each simple summand and hence on all of `V`, giving a canonical degree-`1` character
-- `A →* ℂˣ`. Conversely, such a character yields scalar action by homotheties, and via
-- `MonoidHom.toRepresentation`, the restricted representation is a direct sum of copies of that
-- character, hence isotypic.

/-- Helper for Remark 8-8.1-2: for a module viewed through `Representation.ofModule'`, the
associated group-algebra operator is exactly the original `ℂ[A]`-scalar action. -/
private theorem ofModule'_asAlgebraHom_apply
    (M : Type*) [AddCommGroup M] [Module ℂ M] [Module (MonoidAlgebra ℂ A) M]
    [IsScalarTower ℂ (MonoidAlgebra ℂ A) M]
    (r : MonoidAlgebra ℂ A) (m : M) :
    ((Representation.ofModule' (k := ℂ) (G := A) M).asAlgebraHom r) m = r • m := by
  -- Expand the group-algebra element linearly and verify the claim on monomials.
  refine MonoidAlgebra.induction_on
    (p := fun r : MonoidAlgebra ℂ A =>
      ((Representation.ofModule' (k := ℂ) (G := A) M).asAlgebraHom r) m = r • m) r ?_ ?_ ?_
  · intro a
    simp [Representation.ofModule', MonoidAlgebra.of]
  · intro r s hr hs
    simp [hr, hs, add_smul]
  · intro c r hr
    simp [hr]

/-- Helper for Remark 8-8.1-2: the owner module of `Representation.ofModule' M` is canonically the
original `ℂ[A]`-module `M`. -/
private noncomputable def ofModule'_asModuleLinearEquiv
    (M : Type*) [AddCommGroup M] [Module ℂ M] [Module (MonoidAlgebra ℂ A) M]
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
        -- Transport the `ℂ[A]`-action through `asModuleEquiv`, then identify it with the
        -- original owner action using `ofModule'_asAlgebraHom_apply`.
        calc
          (Representation.ofModule' (k := ℂ) (G := A) M).asModuleEquiv (r • x)
              = ((Representation.ofModule' (k := ℂ) (G := A) M).asAlgebraHom r)
                  ((Representation.ofModule' (k := ℂ) (G := A) M).asModuleEquiv x) := by
                    simpa using
                      (Representation.asModuleEquiv_map_smul
                        (ρ := Representation.ofModule' (k := ℂ) (G := A) M) r x)
          _ = r • (Representation.ofModule' (k := ℂ) (G := A) M).asModuleEquiv x := by
                simp [ofModule'_asAlgebraHom_apply] }

/-- Helper for Remark 8-8.1-2: an equivalence between `Representation.ofModule' M` and `τ`
yields the corresponding owner-level `ℂ[A]`-linear equivalence. -/
private theorem nonempty_moduleLinearEquiv_of_nonempty_equiv_ofModule'
    {W' : Type*} [AddCommGroup W'] [Module ℂ W']
    (τ : Representation ℂ A W')
    {M : Type*} [AddCommGroup M] [Module ℂ M] [Module (MonoidAlgebra ℂ A) M]
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
      refine ⟨(ofModule'_asModuleLinearEquiv (A := A) M).symm (e.symm (τ.asModuleEquiv w)), ?_⟩
      -- Move the target equality back to the ambient `ℂ`-vector-space picture of `τ`.
      change (e ((Representation.ofModule' (k := ℂ) (G := A) M).asModuleEquiv
        ((Representation.ofModule' (k := ℂ) (G := A) M).asModuleEquiv.symm
          (e.symm (τ.asModuleEquiv w)))) : W') =
        (τ.asModuleEquiv w : W')
      simp
  exact ⟨(ofModule'_asModuleLinearEquiv (A := A) M).symm.trans (LinearEquiv.ofBijective f hf_bij)⟩

/-- Helper for Remark 8-8.1-2: a simple owner submodule gives an irreducible restricted
representation. -/
private theorem ofModule'_isIrreducible_of_isSimpleModule
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
        (ofModule'_asModuleLinearEquiv (A := A) m) hm)

/-- Helper for Remark 8-8.1-2: every simple owner summand of the restricted `ℂ[A]`-module is
one-dimensional over `ℂ`. -/
lemma simple_owner_submodule_finrank_eq_one
    [Module (MonoidAlgebra ℂ A) V] [IsScalarTower ℂ (MonoidAlgebra ℂ A) V]
    (m : Submodule (MonoidAlgebra ℂ A) V) [IsSimpleModule (MonoidAlgebra ℂ A) m] :
    Module.finrank ℂ m = 1 := by
  let ρm : Representation ℂ A m := Representation.ofModule' (k := ℂ) (G := A) m
  letI : ρm.IsIrreducible := ofModule'_isIrreducible_of_isSimpleModule (A := A) (V := V) m
  letI : FiniteDimensional ℂ m := IsIrreducible.finiteDimensional_of_finite ρm
  -- The commutativity of `A` makes Schur's lemma force the constituent to have dimension `1`.
  simpa using IsIrreducible.finrank_eq_one_of_isMulCommutative ρm

/-- Helper for Remark 8-8.1-2: a simple owner summand of the restricted `ℂ[A]`-module comes from
a degree-`1` character of `A`. -/
lemma character_of_simple_owner_submodule
    [Module (MonoidAlgebra ℂ A) V] [IsScalarTower ℂ (MonoidAlgebra ℂ A) V]
    (m : Submodule (MonoidAlgebra ℂ A) V) [IsSimpleModule (MonoidAlgebra ℂ A) m] :
    ∃ χ : A →* ℂˣ, ∀ a : A,
      (Representation.ofModule' (k := ℂ) (G := A) m) a = (χ a : ℂ) • 1 := by
  let ρm : Representation ℂ A m := Representation.ofModule' (k := ℂ) (G := A) m
  have hdim : Module.finrank ℂ m = 1 :=
    simple_owner_submodule_finrank_eq_one (A := A) (V := V) m
  -- Choose the scalar by which each endomorphism of the one-dimensional constituent acts.
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
  -- The constituent action is exactly the scalar prescribed by the extracted character.
  simpa [χ] using hα₀_eq a

/-- Helper for Remark 8-8.1-2: a one-dimensional representation acting by the scalars prescribed
by `χ` is equivalent to the degree-`1` representation attached to `χ`. -/
private theorem equiv_character_representation_of_finrank_one_scalar_action
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (τ : Representation ℂ A W) (χ : A →* ℂˣ)
    (hW : Module.finrank ℂ W = 1)
    (hτ : ∀ a : A, τ a = (χ a : ℂ) • 1) :
    Nonempty (τ.Equiv χ.toRepresentation) := by
  let e : W ≃ₗ[ℂ] ℂ := (Module.nonempty_linearEquiv_of_finrank_eq_one hW).some.symm
  -- In a chosen one-dimensional coordinate, both representations act by the same scalar.
  refine ⟨Representation.Equiv.mk e ?_⟩
  intro a
  ext w
  have hw := LinearMap.congr_fun (hτ a) w
  simpa [MonoidHom.toRepresentation, LinearMap.lsmul_apply] using congrArg e hw

/-- Helper for Remark 8-8.1-2: if every owner action of `MonoidAlgebra.single a 1` is the scalar
`χ a`, then every simple owner summand is owner-linearly equivalent to the module of
`χ.toRepresentation`. -/
lemma simple_owner_submodule_equiv_character_module_of_scalar_action
    [Module (MonoidAlgebra ℂ A) V] [IsScalarTower ℂ (MonoidAlgebra ℂ A) V]
    (χ : A →* ℂˣ)
    (hχ : ∀ a : A, ∀ v : V,
      ((MonoidAlgebra.single a (1 : ℂ)) : MonoidAlgebra ℂ A) • v = (χ a : ℂ) • v)
    (m : Submodule (MonoidAlgebra ℂ A) V) [IsSimpleModule (MonoidAlgebra ℂ A) m] :
    Nonempty (m ≃ₗ[MonoidAlgebra ℂ A] χ.toRepresentation.asModule) := by
  let ρm : Representation ℂ A m := Representation.ofModule' (k := ℂ) (G := A) m
  have hdim : Module.finrank ℂ m =
      1 := simple_owner_submodule_finrank_eq_one (A := A) (V := V) m
  have hρm (a : A) : ρm a = (χ a : ℂ) • 1 := by
    -- Restrict the global scalar-action hypothesis from `V` to the simple owner `m`.
    ext x
    simpa using hχ a (x : V)
  have hRep :
      Nonempty (ρm.Equiv χ.toRepresentation) :=
    equiv_character_representation_of_finrank_one_scalar_action
      (τ := ρm) (χ := χ) (hW := hdim) (hτ := hρm)
  -- Convert the representation equivalence back to an owner-level `ℂ[A]`-linear equivalence.
  simpa using
    nonempty_moduleLinearEquiv_of_nonempty_equiv_ofModule'
      (A := A) (τ := χ.toRepresentation) hRep

/-- Remark 8-8.1-2: when `A` is abelian, condition `(b)` of Proposition `8-8.1-1` is equivalent
to saying that the restricted action comes from a single degree-`1` character of `A`,
equivalently that every element of `A` acts on `V` by a homothety. The only semisimplicity input
is the finiteness of the subgroup action on `A`. -/
theorem restriction_isotypic_iff_exists_character_of_commutative_subgroup :
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
  -- Route correction: use the owner-level `finsupp` decomposition directly, then read the scalar
  -- action coordinatewise from one simple constituent instead of pushing a raw scalar formula
  -- through a larger representation-level transport.
  change IsIsotypic (MonoidAlgebra ℂ A) V ↔
    ∃ χ : A →* ℂˣ, ∀ a : A, ρ a = (χ a : ℂ) • 1
  constructor
  · intro hIso
    by_cases hV : Subsingleton V
    · letI : Subsingleton V := hV
      refine ⟨1, ?_⟩
      intro a
      -- On the zero module every endomorphism agrees with every homothety.
      ext v
      exact Subsingleton.elim _ _
    · letI : Nontrivial V := not_subsingleton_iff_nontrivial.mp hV
      obtain ⟨ι, -, S, hSsimple, ⟨e⟩⟩ := hIso.linearEquiv_finsupp
      letI : IsSimpleModule (MonoidAlgebra ℂ A) S := hSsimple
      obtain ⟨χ, hSχ⟩ :=
        character_of_simple_owner_submodule (A := A) (V := V) S
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
    -- Every simple owner summand is equivalent to the same character module, so any two of them
    -- are equivalent to each other.
    intro m _
    intro m' _
    exact
      ⟨(simple_owner_submodule_equiv_character_module_of_scalar_action
          (A := A) (χ := χ) hχmodule m').some.trans
        (simple_owner_submodule_equiv_character_module_of_scalar_action
          (A := A) (χ := χ) hχmodule m).some.symm⟩

end

end

end Representation

/-! ### Remark_8_8_1_4 (from Chap08) -/
/- Source/core/bridge triage:
* source-facing: this remark only records the complex case of the chapter's index bound for an
  irreducible finite-dimensional representation.
* core/canonical: the owner is
  `Representation.finrank_le_index_of_commutative_subgroup` from Corollary `3-3.1-2`.
* bridge/view: no new declaration is needed here, because the remark is exactly the chapter-8
  reading of that upstream owner theorem at `k = ℂ`.

Remark 8-8.1-4: without assuming that `A` is normal, the divisibility statement from Corollary
`8-8.1-3` may fail, but Corollary `3-3.1-2` still gives the index bound for irreducible
finite-dimensional complex representations. -/
recall Representation.finrank_le_index_of_commutative_subgroup

/-! ### Exercise_8_8_2_2 (from Chap08) -/
open CategoryTheory
open scoped BigOperators Representation SubgroupInduction

universe w x

namespace Representation

noncomputable section

section SemidirectAbelian

variable {A : Type} [CommGroup A]
variable {H : Type} [Group H]
variable (φ : H →* MulAut A)

attribute [local instance] Fintype.ofFinite

namespace FDRep

/-- Helper for Exercise 8-8.2-2: bundle LinearRepresentations_Serre_1977's packet `θ[φ; χ, ρ]` as a finite-dimensional
representation so Chapter 2's complete-family API can read its degree and simplicity. -/
noncomputable abbrev theta [Finite H]
    (φ : H →* MulAut A) (χ : A →* ℂˣ) (ρ : FDRep ℂ H_[φ; χ]) :
    FDRep ℂ (A ⋊[φ] H) :=
  FDRep.of (Representation.theta φ χ (Rep.of ρ.ρ)).ρ

end FDRep

/-- Helper for Exercise 8-8.2-2: a semidirect product of finite groups is finite. -/
private theorem semidirectProduct_finite [Finite A] [Finite H] :
    Finite (A ⋊[φ] H) := by
  letI : Fintype A := Fintype.ofFinite A
  letI : Fintype H := Fintype.ofFinite H
  let eprod : A ⋊[φ] H ≃ A × H :=
    { toFun := fun x ↦ (x.1, x.2)
      invFun := fun p ↦ ⟨p.1, p.2⟩
      left_inv := by
        intro x
        cases x
        rfl
      right_inv := by
        intro p
        cases p
        rfl }
  letI : Fintype (A ⋊[φ] H) := Fintype.ofEquiv (A × H) eprod.symm
  exact inferInstance

/-- Helper for Exercise 8-8.2-2: the semidirect product cardinal is nonzero when viewed in `ℂ`. -/
private theorem semidirect_product_card_ne_zero_complex [Finite A] [Finite H] :
    NeZero (Nat.card (A ⋊[φ] H) : ℂ) := by
  let _ : Finite (A ⋊[φ] H) := semidirectProduct_finite (φ := φ)
  exact ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩

/-- Helper for Exercise 8-8.2-2: the subgroup-side packet source already satisfies the two
inputs of LinearRepresentations_Serre_1977's reverse Mackey criterion. -/
private theorem theta_reverse_mackey_hypothesis [Finite A] [Finite H]
    (χ : A →* ℂˣ) (ρ : Rep.{w} ℂ H_[φ; χ]) [ρ.ρ.IsIrreducible] :
    Representation.IsIrreducible (theta_packet_source (φ := φ) χ ρ).ρ ∧
      (∀ s ∉ character_stabilizer_subgroup (φ := φ) χ,
        ∀ f :
          localMackeyTwist (φ := φ)
              (character_stabilizer_subgroup (φ := φ) χ)
              (character_stabilizer_subgroup (φ := φ) χ)
              (theta_packet_source (φ := φ) χ ρ) s ⟶
            Rep.res
              (localMackeySubgroup (φ := φ)
                (character_stabilizer_subgroup (φ := φ) χ)
                (character_stabilizer_subgroup (φ := φ) χ) s).subtype
              (theta_packet_source (φ := φ) χ ρ),
          f = 0) := by
  constructor
  · -- The explicit subgroup model of the packet source is irreducible before induction.
    simpa [theta_packet_source] using
      character_stabilizer_subgroup_source_isIrreducible (φ := φ) χ ρ
  · intro s hs f
    -- Away from the stabilizer subgroup, the Mackey weight mismatch kills every intertwiner.
    exact theta_local_mackey_disjoint (φ := φ) (χ := χ) (ρ := ρ) hs f

/-- Helper for Exercise 8-8.2-2: the explicit induced subgroup model in LinearRepresentations_Serre_1977's proof is
irreducible by the reverse direction of Mackey's criterion. -/
private theorem theta_packet_induction_model_isIrreducible [Finite A] [Finite H]
    (χ : A →* ℂˣ) (ρ : Rep.{w} ℂ H_[φ; χ]) [ρ.ρ.IsIrreducible] :
    (Rep.ind
      (character_stabilizer_subgroup (φ := φ) χ).subtype
      (theta_packet_source (φ := φ) χ ρ)).ρ.IsIrreducible := by
  let _ : Finite (A ⋊[φ] H) := semidirectProduct_finite (φ := φ)
  let _ : NeZero (Nat.card (A ⋊[φ] H) : ℂ) :=
    semidirect_product_card_ne_zero_complex (φ := φ)
  -- Feed the packet source irreducibility and the off-subgroup Mackey vanishing into the
  -- Chapter 7 reverse Mackey criterion.
  refine
    (ind_isIrreducible_iff_isIrreducible_and_mackey_disjoint
      (k := ℂ)
      (G := A ⋊[φ] H)
      (H := character_stabilizer_subgroup (φ := φ) χ)
      (ρ := (theta_packet_source (φ := φ) χ ρ).ρ)).2 ?_
  simpa [localMackeySubgroup, localMackeyTwist] using
    theta_reverse_mackey_hypothesis (φ := φ) χ ρ

/-- Helper for Exercise 8-8.2-2: once the explicit induced packet model is irreducible, the
canonical equivalence with `θ[φ; χ, ρ]` transports irreducibility back to the packet itself. -/
private theorem theta_isIrreducible_of_induction_model_local [Finite H]
    (χ : A →* ℂˣ) (ρ : Rep.{w} ℂ H_[φ; χ])
    (hInd :
      (Rep.ind
        (character_stabilizer_subgroup (φ := φ) χ).subtype
        (theta_packet_source (φ := φ) χ ρ)).ρ.IsIrreducible) :
    (Representation.theta φ χ ρ).ρ.IsIrreducible := by
  letI :
      (Rep.ind
        (character_stabilizer_subgroup (φ := φ) χ).subtype
        (theta_packet_source (φ := φ) χ ρ)).ρ.IsIrreducible :=
    hInd
  -- Transport irreducibility across the canonical `θ ≃ Ind` comparison.
  exact
    isIrreducible_of_nonempty_equiv
      (ρ := (Rep.ind
        (character_stabilizer_subgroup (φ := φ) χ).subtype
        (theta_packet_source (φ := φ) χ ρ)).ρ)
      (σ := (Representation.theta φ χ ρ).ρ)
      ⟨(theta_equiv_ind_character_stabilizer_subgroup (φ := φ) χ ρ).symm⟩

/-- Helper for Exercise 8-8.2-2: in the finite-`A` situation of the exercise, LinearRepresentations_Serre_1977's Mackey criterion
proves that the little-groups packet `θ[φ; χ, ρ]` is irreducible. -/
theorem theta_isIrreducible [Finite A] [Finite H]
    (χ : A →* ℂˣ) (ρ : Rep.{w} ℂ H_[φ; χ]) [ρ.ρ.IsIrreducible] :
    (Representation.theta φ χ ρ).ρ.IsIrreducible := by
  -- Route correction: the compiled Chapter 7 criterion is now available, so we follow LinearRepresentations_Serre_1977's
  -- original route directly on the explicit packet subgroup instead of rebuilding a parallel API.
  have hInd :
      (Rep.ind
        (character_stabilizer_subgroup (φ := φ) χ).subtype
        (theta_packet_source (φ := φ) χ ρ)).ρ.IsIrreducible :=
    theta_packet_induction_model_isIrreducible (φ := φ) χ ρ
  -- Transport irreducibility from the induced subgroup model back to the packet `θ[φ; χ, ρ]`.
  exact theta_isIrreducible_of_induction_model_local (φ := φ) χ ρ hInd

/-- Helper for Exercise 8-8.2-2: LinearRepresentations_Serre_1977's Mackey-criterion proof already closes the packet
irreducibility statement when the normal factor `A` is finite, so the ambient semidirect product
is itself finite. -/
private theorem theta_irreducible_of_finite_normal_factor [Finite A] [Finite H]
    (χ : A →* ℂˣ) (ρ : Rep.{w} ℂ H_[φ; χ]) [ρ.ρ.IsIrreducible] :
    (Representation.theta φ χ ρ).ρ.IsIrreducible := by
  -- This local wrapper keeps the later exercise proofs on the already-established finite-group
  -- route without repeating the transport step.
  exact theta_isIrreducible (φ := φ) χ ρ

/-
Source/core/bridge triage for Exercise 8-8.2-2:
* `source-facing`: the orbit-count and square-degree identities for LinearRepresentations_Serre_1977's little-groups
  construction, and the resulting completeness of the induced family on `A ⋊[φ] H`.
* `core/canonical`: `HasCharacterOrbitRepresentatives`, `FDRep.theta`,
  `IsCompleteIrreducibleFamily`, `sum_sq_degree_eq_card_of_complete_irreducible_family`, and
  `complete_irreducible_family_iff_sum_sq_degree_eq_card`.
* `bridge/view`: `Representation.theta` is the unbundled owner, while `FDRep.theta` is the
  finite-dimensional view needed by the Chapter 2 complete-family owner API.

Primitive data versus derived API: the public input is the orbit-representative family `χ` and,
for each stabilizer, a complete pairwise nonisomorphic irreducible family `ρ`. The finite indexing
needed for the displayed sums is operational data derived from the owner hypotheses, so the theorem
surfaces should stay in the owner-style `∑'` form rather than exposing proof-only finite-sum
bookkeeping.

Sampled owner declarations in this domain:
* `HasCharacterOrbitRepresentatives.finiteIndex`
* `FDRep.theta`
* `IsCompleteIrreducibleFamily.finite_index`
* `sum_sq_degree_eq_card_of_complete_irreducible_family`
* `complete_irreducible_family_iff_sum_sq_degree_eq_card`
-/

section

variable [Finite A]
variable {ι : Type w}

-- Proof sketch: apply the class formula to the `H`-action on the linear characters of `A`, using
-- the chosen orbit representatives `χ i`; the orbit stabilizer of `χ i` is exactly
-- `H_[φ; χ i]`.
/-- Exercise 8-8.2-2 (1): if `χ : ι → (A →* ℂˣ)` is a complete set of
representatives for the `H`-orbits in the character group of `A`, then the
cardinality of that character group is the sum of the subgroup indices
`[H : H_[φ; χ_i]]`. -/
theorem card_character_eq_sum_characterStabilizer_index_of_orbit_representatives
    (χ : ι → A →* ℂˣ) (hχ : HasCharacterOrbitRepresentatives φ χ) :
    Nat.card (A →* ℂˣ) =
      ∑' i : ι, (H_[φ; χ i]).index := by
  classical
  let _ : MulAction H A := MulAction.compHom A φ
  let _ : MulDistribMulAction H A := MulDistribMulAction.compHom A φ
  let _ : MulAction Hᵈᵐᵃ (A →* ℂˣ) := inferInstance
  let _ : MulAction H (A →* ℂˣ) :=
    MulAction.compHom (A →* ℂˣ) (show H →* Hᵈᵐᵃ from (MulEquiv.inv' H).toMonoidHom)
  let _ : Finite ι := HasCharacterOrbitRepresentatives.finiteIndex φ hχ
  have hχ_bijective : Function.Bijective
      (fun i ↦ (Quotient.mk'' (χ i) : MulAction.orbitRel.Quotient H (A →* ℂˣ))) := by
    -- Unfold the orbit-representative owner to recover the quotient parametrization.
    simpa [HasCharacterOrbitRepresentatives] using hχ
  let eχ : ι ≃ MulAction.orbitRel.Quotient H (A →* ℂˣ) := Equiv.ofBijective _ hχ_bijective
  have hfiniteFiber : ∀ i : ι, Finite (H ⧸ MulAction.stabilizer H (χ i)) := by
    intro i
    -- Each stabilizer quotient is equivalent to the corresponding orbit inside the finite
    -- character group.
    exact Finite.of_equiv _ (MulAction.orbitEquivQuotientStabilizer H (χ i))
  calc
    Nat.card (A →* ℂˣ) =
        Nat.card (Σ q : MulAction.orbitRel.Quotient H (A →* ℂˣ),
          H ⧸ MulAction.stabilizer H (χ (eχ.symm q))) := by
          -- Apply the class formula using the chosen representative in each character orbit.
          refine Nat.card_congr ?_
          exact MulAction.selfEquivSigmaOrbitsQuotientStabilizer' H (A →* ℂˣ)
            (φ := fun q ↦ χ (eχ.symm q)) (by
              intro q
              exact eχ.apply_symm_apply q)
    _ = Nat.card (Σ i : ι, H ⧸ MulAction.stabilizer H (χ i)) := by
          -- Transport the sigma-indexing from orbit classes back to the chosen representatives.
          exact Nat.card_congr
            (Equiv.sigmaCongrLeft (β := fun i : ι ↦ H ⧸ MulAction.stabilizer H (χ i))
              eχ.symm)
    _ = ∑ i : ι, Nat.card (H ⧸ MulAction.stabilizer H (χ i)) := by
          -- The sigma-cardinality splits as the sum of the finite fiber cardinalities.
          exact Nat.card_sigma
    _ = ∑' i : ι, (H_[φ; χ i]).index := by
          rw [tsum_fintype]
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [Subgroup.index_eq_card]

end

section

variable {χ : A →* ℂˣ}
variable {κ : Type w}

/-- Helper for Exercise 8-8.2-2: a finite abelian group has as many complex linear characters as
elements. -/
lemma card_linearCharacter_eq_card [Finite A] :
    Nat.card (A →* ℂˣ) = Nat.card A := by
  let e₁ : (A →* ℂˣ) ≃ (A →* ℂ) :=
    (MonoidHom.toHomUnitsMulEquiv (G := A) (M := ℂ)).toEquiv.symm
  let e₂ : (A →* ℂ) ≃ AddChar (Additive A) ℂ :=
    (AddChar.toMonoidHomEquiv (A := Additive A) (M := ℂ)).symm
  let e : (A →* ℂˣ) ≃ AddChar (Additive A) ℂ := e₁.trans e₂
  have hAdditiveCard : Nat.card (Additive A) = Nat.card A := by
    -- Forgetting between multiplicative and additive presentations does not change cardinality.
    refine Nat.card_congr ?_
    exact
      { toFun := fun a ↦ a
        invFun := fun a ↦ a
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
  calc
    Nat.card (A →* ℂˣ) = Nat.card (AddChar (Additive A) ℂ) := Nat.card_congr e
    _ = Nat.card (Additive A) := by
      let _ : Fintype (Additive A) := Fintype.ofFinite (Additive A)
      let _ : Fintype (AddChar (Additive A) ℂ) := Fintype.ofFinite (AddChar (Additive A) ℂ)
      rw [Nat.card_eq_fintype_card, AddChar.card_eq, Nat.card_eq_fintype_card]
    _ = Nat.card A := hAdditiveCard

-- Route correction: this exercise now reuses the canonical induction-bridge API imported from
-- `Proposition_8_8_2_1` instead of maintaining a file-local copy of those declarations.

/-- Helper for Exercise 8-8.2-2: a finite-index induced representation has degree equal to the
subgroup index times the degree of the inducing subspace. -/
private theorem finrank_eq_index_mul_finrank_of_isInducedFromSubrepresentation_local
    {G : Type} [Group G]
    {V : Type} [AddCommGroup V] [Module ℂ V]
    {S : Subgroup G} [Finite (G ⧸ S)]
    (ρ : Representation ℂ G V) [FiniteDimensional ℂ V]
    (W : Subrepresentation (ρ.comp S.subtype))
    (hInduced : ρ.IsInducedFromSubrepresentation S W) :
    Module.finrank ℂ V = S.index * Module.finrank ℂ W.toSubmodule := by
  classical
  letI : DecidableEq (G ⧸ S) := Classical.decEq _
  letI : Fintype (G ⧸ S) := Fintype.ofFinite (G ⧸ S)
  have leftQuotientSubmodule_out_local (q : G ⧸ S) :
      ρ.leftQuotientSubmodule S W q = W.toSubmodule.map (ρ q.out) := by
    have hq := ρ.leftQuotientSubmodule_mk S W q.out
    convert hq using 1
    exact congrArg (ρ.leftQuotientSubmodule S W) (Quotient.out_eq q).symm
  have hInternal : DirectSum.IsInternal (ρ.leftQuotientSubmodule S W) := by
    -- Unpack the Chapter 3 owner predicate into the corresponding internal direct sum.
    simpa [Representation.IsInducedFromSubrepresentation] using hInduced
  letI := DirectSum.IsInternal.chooseDecomposition (ρ.leftQuotientSubmodule S W) hInternal
  letI : ∀ q : G ⧸ S, Module.Free ℂ (ρ.leftQuotientSubmodule S W q) :=
    fun q ↦ Module.Free.of_divisionRing ℂ _
  let e := (DirectSum.decomposeLinearEquiv (ρ.leftQuotientSubmodule S W)).symm
  -- Compare the ambient representation with the direct sum of its left-coset summands.
  calc
    Module.finrank ℂ V =
        Module.finrank ℂ (DirectSum (G ⧸ S) fun q ↦ ρ.leftQuotientSubmodule S W q) := by
          exact e.finrank_eq.symm
    _ = ∑ q : G ⧸ S, Module.finrank ℂ (ρ.leftQuotientSubmodule S W q) := by
          exact Module.finrank_directSum (R := ℂ) (M := fun q ↦ ρ.leftQuotientSubmodule S W q)
    _ = ∑ _q : G ⧸ S, Module.finrank ℂ W.toSubmodule := by
          refine Finset.sum_congr rfl ?_
          intro q hq
          let eW :
              W.toSubmodule ≃ₗ[ℂ] ρ.leftQuotientSubmodule S W q :=
            let eV : V ≃ₗ[ℂ] V := LinearEquiv.ofBijective (ρ q.out) (ρ.apply_bijective q.out)
            (eV.submoduleMap W.toSubmodule).trans
              (LinearEquiv.ofEq _ _ (leftQuotientSubmodule_out_local q).symm)
          simpa using eW.finrank_eq.symm
    _ = S.index * Module.finrank ℂ W.toSubmodule := by
          simp [Subgroup.index_eq_card]

/-- Helper for Exercise 8-8.2-2: ordinary induction from a finite-index subgroup multiplies the
degree by the subgroup index. -/
private theorem ind_finrank_eq_subgroup_index_mul_finrank_local
    {G : Type} [Group G]
    {S : Subgroup G} [Finite (G ⧸ S)]
    {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (σ : Representation ℂ S W) :
    Module.finrank ℂ (Rep.ind S.subtype (Rep.of σ)) = S.index * Module.finrank ℂ W := by
  classical
  letI : S.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  letI : DecidableEq (G ⧸ S) := Classical.decEq _
  let C : Rep ℂ G := Rep.coind S.subtype (Rep.of σ)
  let e :
      ((Rep.ind S.subtype (Rep.of σ)).ρ).Equiv C.ρ :=
    Representation.equivOfIso (Rep.indCoindIso (Rep.of σ))
  let W₀ :
      Subrepresentation (C.ρ.comp S.subtype) :=
    Representation.supportedOnSubgroupSubrepresentation S σ
  let U :
      Subrepresentation (((Rep.ind S.subtype (Rep.of σ)).ρ).comp S.subtype) :=
    transported_subrepresentation_of_equiv (comp_subtype_equiv e.symm S) W₀
  have hW₀ :
      C.ρ.IsInducedFromSubrepresentation S W₀ := by
    -- The coinduced model is already packaged as induced from the subgroup-supported copy.
    simpa [C, W₀] using
      (Representation.isInducedFrom_supportedOnSubgroupSubrepresentation (H := S) (θ := σ))
  have hU :
      ((Rep.ind S.subtype (Rep.of σ)).ρ).IsInducedFromSubrepresentation S U := by
    -- Transport the inducedness witness across the canonical `Ind ≃ Coind` comparison.
    simpa [U] using isInducedFromSubrepresentation_of_equiv e.symm S W₀ hW₀
  let eU :
      W₀.toSubmodule ≃ₗ[ℂ] U.toSubmodule :=
    Submodule.equivMapOfInjective e.symm.toLinearMap e.symm.injective W₀.toSubmodule
  have hUfinrank :
      Module.finrank ℂ U.toSubmodule = Module.finrank ℂ W₀.toSubmodule := by
    -- Transporting along the equivalence only maps the carrier, so finrank is unchanged.
    simpa [U] using eU.finrank_eq.symm
  have hW₀finrank :
      Module.finrank ℂ W₀.toSubmodule = Module.finrank ℂ W := by
    -- The subgroup-supported subrepresentation is canonically equivalent to the source.
    exact (Representation.supportedOnSubgroupEquiv S σ).toLinearEquiv.finrank_eq.symm
  letI : FiniteDimensional ℂ W₀.toSubmodule :=
    FiniteDimensional.of_injective
      (Representation.supportedOnSubgroupEquiv S σ).symm.toLinearMap
      (Representation.supportedOnSubgroupEquiv S σ).symm.injective
  letI : FiniteDimensional ℂ U.toSubmodule :=
    FiniteDimensional.of_injective eU.symm.toLinearMap eU.symm.injective
  letI : ∀ q : G ⧸ S,
      FiniteDimensional ℂ (((Rep.ind S.subtype (Rep.of σ)).ρ).leftQuotientSubmodule S U q) :=
    fun q ↦ by
      have leftQuotientSubmodule_out_local :
          ((Rep.ind S.subtype (Rep.of σ)).ρ).leftQuotientSubmodule S U q =
            U.toSubmodule.map (((Rep.ind S.subtype (Rep.of σ)).ρ) q.out) := by
        have hq :=
          ((Rep.ind S.subtype (Rep.of σ)).ρ).leftQuotientSubmodule_mk S U q.out
        convert hq using 1
        exact
          congrArg (((Rep.ind S.subtype (Rep.of σ)).ρ).leftQuotientSubmodule S U)
            (Quotient.out_eq q).symm
      let eUq :
          U.toSubmodule ≃ₗ[ℂ]
            ((Rep.ind S.subtype (Rep.of σ)).ρ).leftQuotientSubmodule S U q :=
        let eV :
            Rep.ind S.subtype (Rep.of σ) ≃ₗ[ℂ] Rep.ind S.subtype (Rep.of σ) :=
          LinearEquiv.ofBijective
            (((Rep.ind S.subtype (Rep.of σ)).ρ) q.out)
            (((Rep.ind S.subtype (Rep.of σ)).ρ).apply_bijective q.out)
        (eV.submoduleMap U.toSubmodule).trans
          (LinearEquiv.ofEq _ _ leftQuotientSubmodule_out_local.symm)
      exact FiniteDimensional.of_injective eUq.symm.toLinearMap eUq.symm.injective
  have hInternalU :
      DirectSum.IsInternal
        (((Rep.ind S.subtype (Rep.of σ)).ρ).leftQuotientSubmodule S U) := by
    simpa [Representation.IsInducedFromSubrepresentation] using hU
  letI := DirectSum.IsInternal.chooseDecomposition
    (((Rep.ind S.subtype (Rep.of σ)).ρ).leftQuotientSubmodule S U) hInternalU
  letI : FiniteDimensional ℂ
      (DirectSum (G ⧸ S)
        fun q ↦ ((Rep.ind S.subtype (Rep.of σ)).ρ).leftQuotientSubmodule S U q) := by
    infer_instance
  let eDecomp :=
    (DirectSum.decomposeLinearEquiv
      (((Rep.ind S.subtype (Rep.of σ)).ρ).leftQuotientSubmodule S U)).symm
  letI : FiniteDimensional ℂ (Rep.ind S.subtype (Rep.of σ)) :=
    FiniteDimensional.of_injective eDecomp.symm.toLinearMap eDecomp.symm.injective
  calc
    Module.finrank ℂ (Rep.ind S.subtype (Rep.of σ)) = S.index * Module.finrank ℂ U.toSubmodule := by
          exact
            finrank_eq_index_mul_finrank_of_isInducedFromSubrepresentation_local
              ((Rep.ind S.subtype (Rep.of σ)).ρ) U hU
    _ = S.index * Module.finrank ℂ W₀.toSubmodule := by rw [hUfinrank]
    _ = S.index * Module.finrank ℂ W := by rw [hW₀finrank]

/-- Helper for Exercise 8-8.2-2: the explicit packet subgroup has the same index in `A ⋊[φ] H`
as the stabilizer has in `H`. -/
private theorem character_stabilizer_subgroup_index_eq
    (χ : A →* ℂˣ) :
    (character_stabilizer_subgroup (φ := φ) χ).index = (H_[φ; χ]).index := by
  classical
  let equot :
      (A ⋊[φ] H) ⧸ character_stabilizer_subgroup (φ := φ) χ ≃ H ⧸ H_[φ; χ] := by
    simpa [character_stabilizer_subgroup_eq_comap (φ := φ) χ] using
      (comap_leftCosetEquiv_of_surjective
        (SemidirectProduct.rightHom : A ⋊[φ] H →* H)
        SemidirectProduct.rightHom_surjective
        (H_[φ; χ]))
  calc
    (character_stabilizer_subgroup (φ := φ) χ).index =
        Nat.card ((A ⋊[φ] H) ⧸ character_stabilizer_subgroup (φ := φ) χ) := by
          rw [Subgroup.index_eq_card]
    _ = Nat.card (H ⧸ H_[φ; χ]) := Nat.card_congr equot
    _ = (H_[φ; χ]).index := by
          rw [Subgroup.index_eq_card]

variable [Finite H]

/-- Helper for Exercise 8-8.2-2: the degree of a little-groups packet is the stabilizer index
times the degree of the stabilizer representation. -/
private theorem theta_finrank_eq_characterStabilizer_index_mul_finrank
    (ρ : FDRep ℂ H_[φ; χ]) :
    Module.finrank ℂ (FDRep.theta φ χ ρ) =
      (H_[φ; χ]).index * Module.finrank ℂ ρ := by
  classical
  let τ : Rep ℂ H_[φ; χ] := Rep.of ρ.ρ
  let Sχ : Subgroup (A ⋊[φ] H) := character_stabilizer_subgroup (φ := φ) χ
  let _ : Finite ((A ⋊[φ] H) ⧸ Sχ) :=
    character_stabilizer_subgroup_quotient_finite (φ := φ) χ
  letI : FiniteDimensional ℂ (stabilizerRepresentation φ χ τ) := by
    -- The imported packet source still uses the same carrier as `ρ`, so no new dimension data
    -- is needed beyond the finite-dimensionality of `ρ`.
    change FiniteDimensional ℂ τ
    infer_instance
  -- Replace `theta` by ordinary induction from the explicit subgroup model and apply the
  -- finite-index induced-dimension formula.
  calc
    Module.finrank ℂ (FDRep.theta φ χ ρ) =
        Module.finrank ℂ
          (Rep.ind Sχ.subtype
            (Rep.of
              ((stabilizerRepresentation φ χ τ).ρ.comp
                (character_stabilizer_subgroup_equiv (φ := φ) χ).symm.toMonoidHom))) := by
          simpa [FDRep.theta, τ, Sχ] using
            (theta_equiv_ind_character_stabilizer_subgroup (φ := φ) χ τ).toLinearEquiv.finrank_eq
    _ = Sχ.index * Module.finrank ℂ ρ := by
          simpa [τ, Sχ] using
            (ind_finrank_eq_subgroup_index_mul_finrank_local
              (S := Sχ)
              (σ := (stabilizerRepresentation φ χ τ).ρ.comp
                (character_stabilizer_subgroup_equiv (φ := φ) χ).symm.toMonoidHom))
    _ = (H_[φ; χ]).index * Module.finrank ℂ ρ := by
          rw [character_stabilizer_subgroup_index_eq (φ := φ) χ]

/-- Helper for Exercise 8-8.2-2: a packet isomorphism between chosen orbit representatives forces
the representatives to agree and then identifies the stabilizer-side irreducible factors. -/
private theorem theta_iso_imp_eq_and_iso_local
    {ι : Type*} (χ : ι → A →* ℂˣ) (hχ : HasCharacterOrbitRepresentatives φ χ)
    {i i' : ι}
    (ρ : Rep.{w} ℂ H_[φ; χ i]) (ρ' : Rep.{w} ℂ H_[φ; χ i'])
    [ρ.ρ.IsIrreducible] [ρ'.ρ.IsIrreducible]
    (e :
      Representation.theta φ (χ i) ρ ≅
        Representation.theta φ (χ i') ρ') :
    ∃ h : i = i', Nonempty (ρ ≅ h ▸ ρ') := by
  let eθ :
      (Representation.theta φ (χ i) ρ).ρ.Equiv
        (Representation.theta φ (χ i') ρ').ρ :=
    Representation.equivOfIso e
  let eWeight :
      (character_weight_subrepresentation
        (φ := φ) (Representation.theta φ (χ i) ρ) (χ i)).ρ.Equiv
        (character_weight_subrepresentation
          (φ := φ) (Representation.theta φ (χ i') ρ') (χ i)).ρ :=
    character_weight_subrepresentation_equiv_of_equiv (φ := φ) eθ (χ i)
  have hsource_weight_irreducible :
      ((character_weight_subrepresentation
        (φ := φ) (Representation.theta φ (χ i) ρ) (χ i)).ρ).IsIrreducible := by
    -- The distinguished `χ_i`-weight space of the source packet recovers `ρ`.
    exact theta_character_weight_subrepresentation_isIrreducible (φ := φ) (χ i) ρ
  letI :
      ((character_weight_subrepresentation
        (φ := φ) (Representation.theta φ (χ i) ρ) (χ i)).ρ).IsIrreducible :=
    hsource_weight_irreducible
  letI :
      Nontrivial
        (character_weight_subrepresentation
          (φ := φ) (Representation.theta φ (χ i) ρ) (χ i)).V :=
    nontrivial_of_isIrreducible
      ((character_weight_subrepresentation
        (φ := φ) (Representation.theta φ (χ i) ρ) (χ i)).ρ)
  obtain ⟨x, hx⟩ := exists_ne
    (0 :
      (character_weight_subrepresentation
        (φ := φ) (Representation.theta φ (χ i) ρ) (χ i)).V)
  let y :
      (character_weight_subrepresentation
        (φ := φ) (Representation.theta φ (χ i') ρ') (χ i)).V :=
    eWeight x
  have hy : y ≠ 0 := by
    intro hy
    exact hx <| eWeight.injective <| by simpa [y] using hy
  have htarget_weight_ne_bot :
      character_weight_submodule
        (φ := φ) (Representation.theta φ (χ i') ρ') (χ i) ≠ ⊥ := by
    rw [Submodule.ne_bot_iff]
    refine ⟨y.1, y.2, ?_⟩
    intro hy0
    exact hy <| Subtype.ext hy0
  let _ := characterMulAction φ
  rcases theta_weight_nonzero_imp_mem_orbit
      (φ := φ) (χ := χ i') (ρ := ρ') (ψ := χ i) htarget_weight_ne_bot with
    ⟨h, hh⟩
  have horbit :
      (Quotient.mk'' (χ i) : MulAction.orbitRel.Quotient H (A →* ℂˣ)) =
        Quotient.mk'' (χ i') := by
    apply Quotient.sound
    refine ⟨h, ?_⟩
    simpa [transportedCharacter] using hh
  have hii : i = i' := hχ.injective horbit
  subst hii
  let eWeight' :
      (character_weight_subrepresentation
        (φ := φ) (Representation.theta φ (χ i) ρ) (χ i)).ρ.Equiv
        (character_weight_subrepresentation
          (φ := φ) (Representation.theta φ (χ i) ρ') (χ i)).ρ :=
    character_weight_subrepresentation_equiv_of_equiv (φ := φ)
      (Representation.equivOfIso e) (χ i)
  let eρ :
      ρ.ρ.Equiv ρ'.ρ :=
    (theta_character_weight_subrepresentation_equiv (φ := φ) (χ i) ρ).symm.trans
      (eWeight'.trans
        (theta_character_weight_subrepresentation_equiv (φ := φ) (χ i) ρ'))
  have hρ_iso : ρ ≅ ρ' := by
    exact Rep.mkIso eρ
  exact ⟨rfl, ⟨hρ_iso⟩⟩

/-- Helper for Exercise 8-8.2-2: the sigma-family of packets indexed by orbit representatives is
pairwise nonisomorphic. -/
private theorem theta_sigma_pairwise_nonisomorphic_of_orbit_representatives
    {κ : ι → Type x}
    (χ : ι → A →* ℂˣ) (hχ : HasCharacterOrbitRepresentatives φ χ)
    (ρ : ∀ i, κ i → FDRep ℂ H_[φ; χ i])
    (hρ_complete : ∀ i, IsCompleteIrreducibleFamily (ρ i))
    (hρ_pairwise : ∀ i, PairwiseNonisomorphic (ρ i)) :
    PairwiseNonisomorphic
      (fun ij : Σ i, κ i ↦ FDRep.theta φ (χ ij.1) (ρ ij.1 ij.2)) := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ hij hθ
  letI : Simple (ρ i j) := (hρ_complete i).isSimple j
  letI : Simple (ρ i' j') := (hρ_complete i').isSimple j'
  letI : Representation.IsIrreducible (ρ i j).ρ :=
    FDRep.isIrreducible_of_simple (ρ i j)
  letI : Representation.IsIrreducible (ρ i' j').ρ :=
    FDRep.isIrreducible_of_simple (ρ i' j')
  rcases hθ with ⟨eθ⟩
  let eRep :
      Representation.theta φ (χ i) (Rep.of (ρ i j).ρ) ≅
        Representation.theta φ (χ i') (Rep.of (ρ i' j').ρ) :=
    (forget₂ (FDRep ℂ (A ⋊[φ] H)) (Rep ℂ (A ⋊[φ] H))).mapIso eθ
  -- Proposition `8-8.2-1 (2)` first forces equality of the orbit representative index.
  rcases theta_iso_imp_eq_and_iso_local
      (φ := φ) χ hχ (i := i) (i' := i')
      (Rep.of (ρ i j).ρ) (Rep.of (ρ i' j').ρ)
      eRep with
    ⟨hii, hijj⟩
  subst hii
  rcases hijj with ⟨eρ⟩
  have hjj : j = j' := by
    by_contra hne
    exact hρ_pairwise i hne <| by
      simpa using ⟨(Representation.equivOfIso eρ).toFDRepIso⟩
  subst hjj
  exact hij rfl

-- Proof sketch: apply Chapter 2's square-degree formula to the stabilizer `H_[φ; χ]`, then use
-- the degree formula `dim θ[φ; χ, ρ_j] = (|H| / |H_[φ; χ]|) * dim ρ_j` to factor out the
-- constant index.
/-- Part (2) of Exercise 8-8.2-2: if `ρ j` runs through a complete family of pairwise nonisomorphic
irreducible finite-dimensional complex representations of `H_[φ; χ]`, then the corresponding
induced representations `θ[φ; χ, ρ j]` satisfy
`∑_j (dim θ[φ; χ, ρ_j])^2 = |H| · [H : H_[φ; χ]]`, equivalently
`|H|^2 / |H_[φ; χ]|`. -/
theorem sum_sq_degree_theta_eq_card_mul_characterStabilizer_index
    (ρ : κ → FDRep ℂ H_[φ; χ])
    (hρ_complete : IsCompleteIrreducibleFamily ρ)
    (hρ_pairwise : PairwiseNonisomorphic ρ) :
    ∑' j : κ, Module.finrank ℂ (FDRep.theta φ χ (ρ j)) ^ 2 =
      Nat.card H * (H_[φ; χ]).index := by
  classical
  letI : NeZero (Nat.card H_[φ; χ] : ℂ) :=
    ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  let _ : Finite κ := IsCompleteIrreducibleFamily.finite_index ρ hρ_complete hρ_pairwise
  let _ : Fintype κ := Fintype.ofFinite κ
  -- Rewrite the packet degrees through the explicit degree formula and factor out the constant
  -- index square from the stabilizer square-degree sum.
  rw [tsum_fintype]
  calc
    ∑ j : κ, Module.finrank ℂ (FDRep.theta φ χ (ρ j)) ^ 2 =
        ∑ j : κ, ((H_[φ; χ]).index * Module.finrank ℂ (ρ j)) ^ 2 := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          rw [theta_finrank_eq_characterStabilizer_index_mul_finrank (φ := φ) (χ := χ) (ρ := ρ j)]
    _ = (H_[φ; χ]).index ^ 2 * ∑ j : κ, Module.finrank ℂ (ρ j) ^ 2 := by
          simp_rw [mul_pow]
          rw [Finset.mul_sum]
    _ = (H_[φ; χ]).index ^ 2 * Nat.card H_[φ; χ] := by
          rw [sum_sq_degree_eq_card_of_complete_irreducible_family ρ hρ_complete hρ_pairwise]
    _ = Nat.card H * (H_[φ; χ]).index := by
          rw [pow_two, mul_assoc, Subgroup.index_mul_card, Nat.mul_comm]

end

section

variable [Finite A] [Finite H]
variable {ι : Type w}
variable (χ : ι → A →* ℂˣ) (hχ : HasCharacterOrbitRepresentatives φ χ)
variable {κ : ι → Type x}

-- Proof sketch: for each orbit representative `χ i`, apply part (2) to a complete irreducible
-- family on `H_[φ; χ i]`; then part (1) shows that the total square-degree sum over all
-- `θ[φ; χ i, ρ]` equals `|A ⋊[φ] H|`, and
-- Remark `complete_irreducible_family_iff_sum_sq_degree_eq_card` gives completeness.
-- This recovers Proposition `8-8.2-1 (3)` by the Chapter 2 criterion.
/-- Part (3) of Exercise 8-8.2-2: let `χ : ι → (A →* ℂˣ)` be a complete set of
orbit representatives for the `H`-action on the linear characters of `A`, and
for each `i` let `ρ i` be a complete family of pairwise nonisomorphic
irreducible finite-dimensional complex representations of `H_[φ; χ i]`. Then
the bundled little-groups family `FDRep.theta φ (χ i) (ρ i j)`, corresponding
to `θ[φ; χ i, ρ]`, is complete for `A ⋊[φ] H`, giving another proof of
Proposition `8-8.2-1 (3)`. -/
theorem theta_family_isCompleteIrreducibleFamily_of_orbit_representatives
    (hχ : HasCharacterOrbitRepresentatives φ χ)
    (ρ : ∀ i, κ i → FDRep ℂ H_[φ; χ i])
    (hρ_complete : ∀ i, IsCompleteIrreducibleFamily (ρ i))
    (hρ_pairwise : ∀ i, PairwiseNonisomorphic (ρ i)) :
    IsCompleteIrreducibleFamily
      (fun ij : Σ i, κ i ↦ FDRep.theta φ (χ ij.1) (ρ ij.1 ij.2)) := by
  classical
  let _ : Finite ι := HasCharacterOrbitRepresentatives.finiteIndex φ hχ
  let _ : Fintype ι := Fintype.ofFinite ι
  let _ : ∀ i, NeZero (Nat.card H_[φ; χ i] : ℂ) := fun i ↦
    ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  let _ : ∀ i, Finite (κ i) := fun i ↦
    IsCompleteIrreducibleFamily.finite_index (ρ i) (hρ_complete i) (hρ_pairwise i)
  let π : (Σ i, κ i) → FDRep ℂ (A ⋊[φ] H) := fun ij ↦
    FDRep.theta φ (χ ij.1) (ρ ij.1 ij.2)
  have hθ_simple :
      ∀ ij : Σ i, κ i, Simple (π ij) := by
    rintro ⟨i, j⟩
    -- Each packet is simple because Proposition `8-8.2-1 (1)` makes its underlying
    -- representation irreducible.
    letI : Simple (ρ i j) := (hρ_complete i).isSimple j
    letI : Representation.IsIrreducible (ρ i j).ρ :=
      FDRep.isIrreducible_of_simple (ρ i j)
    letI : Representation.IsIrreducible (FDRep.theta φ (χ i) (ρ i j)).ρ := by
      simpa [FDRep.theta] using
        (Representation.theta_irreducible_of_finite_normal_factor
          (φ := φ) (χ := χ i) (ρ := Rep.of (ρ i j).ρ))
    simpa [π] using FDRep.simple_of_isIrreducible (FDRep.theta φ (χ i) (ρ i j))
  have hθ_pairwise : PairwiseNonisomorphic π := by
    -- Reuse the packet-separation theorem already proved above.
    simpa [π] using
      (theta_sigma_pairwise_nonisomorphic_of_orbit_representatives
        (φ := φ) χ hχ ρ hρ_complete hρ_pairwise)
  let _ : Finite (A ⋊[φ] H) := by
    exact
      Finite.of_equiv (A × H)
        (SemidirectProduct.equivProd (N := A) (G := H) (φ := φ)).symm
  letI : NeZero (Nat.card (A ⋊[φ] H) : ℂ) :=
    ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  -- The Chapter 2 square-degree criterion upgrades the simple pairwise family to completeness.
  have hcharacter_count :
      ∑ i : ι, (H_[φ; χ i]).index = Nat.card (A →* ℂˣ) := by
    let _ : Fintype ι := Fintype.ofFinite ι
    calc
      ∑ i : ι, (H_[φ; χ i]).index = ∑' i : ι, (H_[φ; χ i]).index := by
        rw [tsum_fintype]
      _ = Nat.card (A →* ℂˣ) := by
        simpa using
          (card_character_eq_sum_characterStabilizer_index_of_orbit_representatives
            (φ := φ) (χ := χ) hχ).symm
  have hθ_complete : IsCompleteIrreducibleFamily π := by
    refine
      (complete_irreducible_family_iff_sum_sq_degree_eq_card
        (π := π) hθ_simple hθ_pairwise).2 ?_
    let sigmaFintype : Fintype (Σ i, κ i) := Fintype.ofFinite (Σ i, κ i)
    let _ : Fintype (Σ i, κ i) := sigmaFintype
    let s : Finset (Σ i, κ i) := Finset.univ
    let _ : ∀ i, Fintype (κ i) := fun i ↦ Fintype.ofFinite (κ i)
    have hs : s = Finset.univ.sigma (fun i ↦ (Finset.univ : Finset (κ i))) := by
      ext ij
      simp [s]
    -- Reindex the sigma-family by orbit representative, evaluate each inner sum with part (2),
    -- and then use part (1) plus `|Â| = |A|`.
    have hsum_explicit :
        s.sum (fun ij : Σ i, κ i ↦ Module.finrank ℂ (π ij) ^ 2) =
          Nat.card (A ⋊[φ] H) := by
      rw [hs, Finset.sum_sigma]
      calc
        ∑ i : ι, ∑ j : κ i, Module.finrank ℂ (π ⟨i, j⟩) ^ 2 =
            ∑ i : ι, Nat.card H * (H_[φ; χ i]).index := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              calc
                ∑ j : κ i, Module.finrank ℂ (π ⟨i, j⟩) ^ 2 =
                    ∑' j : κ i, Module.finrank ℂ (π ⟨i, j⟩) ^ 2 := by
                      rw [tsum_fintype]
                _ = Nat.card H * (H_[φ; χ i]).index := by
                      simpa [π] using
                        (sum_sq_degree_theta_eq_card_mul_characterStabilizer_index
                          (φ := φ) (χ := χ i) (ρ := ρ i) (hρ_complete := hρ_complete i)
                          (hρ_pairwise := hρ_pairwise i))
        _ = Nat.card H * ∑ i : ι, (H_[φ; χ i]).index := by
              rw [← Finset.mul_sum]
        _ = Nat.card H * Nat.card (A →* ℂˣ) := by
              rw [hcharacter_count]
        _ = Nat.card H * Nat.card A := by
              rw [card_linearCharacter_eq_card (A := A)]
        _ = Nat.card (A ⋊[φ] H) := by
              rw [SemidirectProduct.card, Nat.mul_comm]
    simpa [s] using hsum_explicit
  simpa [π] using hθ_complete

end

end SemidirectAbelian

end

end Representation

/-! ### Exercise_8_8_2_3 (from Chap08) -/
open Equiv

local notation "A4" => alternatingGroup (Fin 4)
local notation "S4" => Perm (Fin 4)
local notation "V4" => alternatingGroup.kleinFour (Fin 4)

local instance : (V4).Normal :=
  alternatingGroup.normal_kleinFour (show Nat.card (Fin 4) = 4 by simp)

/- `A₄` already comes with the canonical normal Klein four subgroup `alternatingGroup.kleinFour
(Fin 4)`, so the source-facing refinement should expose that owner directly rather than an
anonymous abelian normal subgroup. The corresponding subgroup of `S₄` is only a bridge/view,
obtained by mapping the canonical owner along the inclusion `A₄ ↪ S₄`. -/
local notation "V4InS4" => Subgroup.map (Subgroup.subtype A4) V4

/- Source/core/bridge triage for Exercise 8-8.2-3:
* `source-facing`: the existence of subgroup complements realizing LinearRepresentations_Serre_1977's semidirect-product
  decompositions for `D_n`, `A₄`, and `S₄`.
* `core/canonical`: the rotation subgroup owner `Subgroup.zpowers (DihedralGroup.r (1 : ZMod n))`,
  the canonical Klein four subgroup owner `alternatingGroup.kleinFour (Fin 4)`, and the
  complement owner `Subgroup.IsComplement'`.
* `bridge/view`: `V4InS4` is the image of the canonical owner `V4 ≤ A₄` under the inclusion
  `A₄ ↪ S₄`.

Primitive data versus derived API: the existence of a complementary subgroup is primitive
source-facing data, while the ambient semidirect-product equivalence comes later from the canonical
bridge `SemidirectProduct.mulEquivSubgroup`. In part `(5)`, the subgroup isomorphism to `S₃`
should therefore be exposed directly as data, rather than wrapped in `Nonempty`. -/

section Dihedral

variable (n : ℕ)

local notation "Rot" => Subgroup.zpowers (DihedralGroup.r (1 : ZMod n))

-- Proof sketch: conjugation by a rotation preserves the cyclic subgroup generated by `r 1`
-- trivially, and conjugation by a reflection inverts the generator, which still lies in the same
-- cyclic subgroup.
/-- Exercise 8-8.2-3 (1): the rotation subgroup of `D_n` is normal. -/
theorem dihedralGroup_rotationSubgroup_normal :
    (Rot).Normal := by
  refine ⟨?_⟩
  intro x hx g
  -- Every element of `Rot` is a power of the basic rotation, so conjugation reduces to the
  -- generator case.
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rcases g with i | i
  · -- Rotations centralize the rotation subgroup.
    rw [DihedralGroup.r_one_zpow, DihedralGroup.inv_r, DihedralGroup.r_mul_r, DihedralGroup.r_mul_r]
    simpa [sub_eq_add_neg, add_assoc] using
      (Subgroup.zpow_mem Rot (Subgroup.mem_zpowers _) k)
  · -- A reflection sends `r^k` to `r^{-k}`, which still lies in the same cyclic subgroup.
    rw [DihedralGroup.r_one_zpow, DihedralGroup.sr_mul_r, DihedralGroup.inv_sr,
      DihedralGroup.sr_mul_sr]
    simpa [sub_eq_add_neg, add_assoc] using
      (Subgroup.zpow_mem Rot (Subgroup.mem_zpowers _) (-k))

-- Proof sketch: take the order-two subgroup generated by a reflection and show that it
-- complements the rotation subgroup. Together with part `(1)`, this yields the canonical
-- semidirect-product bridge `SemidirectProduct.mulEquivSubgroup`.
/-- Exercise 8-8.2-3 (2): the rotation subgroup of `D_n` admits a complementary subgroup of order
`2`. -/
theorem dihedralGroup_hasAbelianSemidirectDecomposition :
    ∃ H : Subgroup (DihedralGroup n),
      (Rot).IsComplement' H ∧
        Nat.card H = 2 := by
  let Ref : Subgroup (DihedralGroup n) := Subgroup.zpowers (DihedralGroup.sr (0 : ZMod n))
  refine ⟨Ref, ?_, ?_⟩
  · -- The subgroup generated by the reflection `sr 0` meets `Rot` trivially and every dihedral
    -- element is either a rotation or a rotation times `sr 0`.
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [Subgroup.disjoint_def]
      intro x hxRot hxRef
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxRef
      rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
      · have hk' : DihedralGroup.sr (0 : ZMod n) ^ (2 * m) = x := by
          simpa [two_mul] using hk
        rw [zpow_mul,
          show DihedralGroup.sr (0 : ZMod n) ^ (2 : ℤ) = 1 by
            norm_num [zpow_ofNat, pow_two, DihedralGroup.sr_mul_self],
          one_zpow] at hk'
        simp [hk']
      · exfalso
        have hsr : x = DihedralGroup.sr (0 : ZMod n) := by
          rw [show (2 * m + 1 : ℤ) = 2 * m + 1 by ring, zpow_add, zpow_mul,
            show DihedralGroup.sr (0 : ZMod n) ^ (2 : ℤ) = 1 by
              norm_num [zpow_ofNat, pow_two, DihedralGroup.sr_mul_self],
            one_zpow] at hk
          simp at hk
          simp [hk]
        obtain ⟨r, hr⟩ := Subgroup.mem_zpowers_iff.mp hxRot
        rw [DihedralGroup.r_one_zpow] at hr
        simp [hsr] at hr
    · apply Set.eq_univ_of_forall
      intro g
      rcases g with i | i
      · refine ⟨DihedralGroup.r i, ?_, 1, Subgroup.one_mem _, by simp⟩
        exact Subgroup.mem_zpowers_iff.mpr ⟨i.cast, by
          simp [ZMod.intCast_zmod_cast i]⟩
      · refine ⟨DihedralGroup.r (-i), ?_, DihedralGroup.sr 0, ?_, ?_⟩
        · exact Subgroup.mem_zpowers_iff.mpr ⟨-i.cast, by
            simp [ZMod.intCast_zmod_cast i]⟩
        · change DihedralGroup.sr (0 : ZMod n) ∈ Ref
          exact Subgroup.mem_zpowers (DihedralGroup.sr (0 : ZMod n))
        · simp
  · -- The reflection subgroup is cyclic of order `2`.
    change Nat.card (Subgroup.zpowers (DihedralGroup.sr (0 : ZMod n))) = 2
    rw [Nat.card_zpowers, DihedralGroup.orderOf_sr]

end Dihedral

/-- Helper for Exercise 8-8.2-3: the point stabilizer of `3` in `S₄` restricts to a permutation
of the complementary three-point set. -/
noncomputable def s4_stabilizer_three_to_subtype_perm :
    MulAction.stabilizer S4 (3 : Fin 4) →* Perm { x : Fin 4 // x ≠ 3 } where
  toFun σ :=
    (σ : S4).subtypePerm (p := fun y : Fin 4 => y ≠ 3) <| by
      have hfix : (σ : S4) 3 = 3 := MulAction.mem_stabilizer_iff.mp σ.property
      intro x
      constructor
      · intro hy hx3
        exact hy (hx3 ▸ hfix)
      · intro hy hσx
        exact hy <| (σ : S4).injective (hσx.trans hfix.symm)
  map_one' := by
    ext x
    rfl
  map_mul' σ τ := by
    ext x
    rfl

/-- Helper for Exercise 8-8.2-3: restricting a permutation in the stabilizer of `3` identifies
that stabilizer with the full permutation group on the remaining three points. -/
noncomputable def s4_stabilizer_three_mulEquiv_subtype_perm :
    MulAction.stabilizer S4 (3 : Fin 4) ≃* Perm { x : Fin 4 // x ≠ 3 } :=
  MulEquiv.ofBijective s4_stabilizer_three_to_subtype_perm <| by
    constructor
    · intro σ τ hστ
      apply Subtype.ext
      -- Two stabilizer elements are equal once their restrictions away from the fixed point agree.
      have hfixσ : (σ : S4) 3 = 3 := MulAction.mem_stabilizer_iff.mp σ.property
      have h1σ : ∀ y : Fin 4, ((σ : S4) y ≠ 3) ↔ y ≠ 3 := by
        intro y
        constructor
        · intro hy hy3
          exact hy (hy3 ▸ hfixσ)
        · intro hy hσy
          exact hy ((σ : S4).injective (hσy.trans hfixσ.symm))
      have h2σ : ∀ y : Fin 4, (σ : S4) y ≠ y → y ≠ 3 := by
        intro y hy hy3
        exact hy (hy3 ▸ hfixσ)
      have hfixτ : (τ : S4) 3 = 3 := MulAction.mem_stabilizer_iff.mp τ.property
      have h1τ : ∀ y : Fin 4, ((τ : S4) y ≠ 3) ↔ y ≠ 3 := by
        intro y
        constructor
        · intro hy hy3
          exact hy (hy3 ▸ hfixτ)
        · intro hy hτy
          exact hy ((τ : S4).injective (hτy.trans hfixτ.symm))
      have h2τ : ∀ y : Fin 4, (τ : S4) y ≠ y → y ≠ 3 := by
        intro y hy hy3
        exact hy (hy3 ▸ hfixτ)
      exact
        (Equiv.Perm.ofSubtype_subtypePerm (p := fun y : Fin 4 => y ≠ 3) h1σ h2σ).symm.trans
          ((congrArg Perm.ofSubtype hστ).trans
            (Equiv.Perm.ofSubtype_subtypePerm (p := fun y : Fin 4 => y ≠ 3) h1τ h2τ))
    · intro u
      -- Extending a permutation of the three-point complement by the identity on `3` lands back
      -- in the stabilizer, and restriction recovers the original permutation.
      refine ⟨⟨u.ofSubtype, ?_⟩, ?_⟩
      · rw [MulAction.mem_stabilizer_iff]
        exact Equiv.Perm.ofSubtype_apply_of_not_mem (p := fun x : Fin 4 => x ≠ 3) u (by simp)
      · simpa [s4_stabilizer_three_to_subtype_perm] using
          (Equiv.Perm.subtypePerm_ofSubtype (p := fun y : Fin 4 => y ≠ 3) u)

/-- Helper for Exercise 8-8.2-3: transport permutations of the complement of `3` to permutations
of `Fin 3`. -/
noncomputable def s4_subtype_perm_mulEquiv_s3 :
    Perm { x : Fin 4 // x ≠ 3 } ≃* Perm (Fin 3) where
  toEquiv := (Equiv.permCongr (finSuccAboveEquiv (3 : Fin 4))).symm
  map_mul' σ τ := by
    ext x
    simp [Equiv.permCongr_apply]

/-- Helper for Exercise 8-8.2-3: the three double transpositions in `S₄`. -/
abbrev s4_doubleTransposition_zero_one : S4 :=
  Equiv.swap 0 1 * Equiv.swap 2 3

/-- Helper for Exercise 8-8.2-3: the three double transpositions in `S₄`. -/
abbrev s4_doubleTransposition_zero_two : S4 :=
  Equiv.swap 0 2 * Equiv.swap 1 3

/-- Helper for Exercise 8-8.2-3: the three double transpositions in `S₄`. -/
abbrev s4_doubleTransposition_zero_three : S4 :=
  Equiv.swap 0 3 * Equiv.swap 1 2

/-- Helper for Exercise 8-8.2-3: the double transposition swapping `0,1` and `2,3` lies in the
canonical Klein four subgroup of `S₄`. -/
lemma s4_doubleTransposition_zero_one_mem :
    s4_doubleTransposition_zero_one ∈ V4InS4 := by
  refine Subgroup.mem_map.2 ?_
  refine ⟨⟨s4_doubleTransposition_zero_one, by
      simp [s4_doubleTransposition_zero_one, Equiv.Perm.mem_alternatingGroup]⟩, ?_, rfl⟩
  rw [← SetLike.mem_coe]
  rw [alternatingGroup.coe_kleinFour_of_card_eq_four (show Nat.card (Fin 4) = 4 by simp)]
  right
  decide

/-- Helper for Exercise 8-8.2-3: the double transposition swapping `0,2` and `1,3` lies in the
canonical Klein four subgroup of `S₄`. -/
lemma s4_doubleTransposition_zero_two_mem :
    s4_doubleTransposition_zero_two ∈ V4InS4 := by
  refine Subgroup.mem_map.2 ?_
  refine ⟨⟨s4_doubleTransposition_zero_two, by
      simp [s4_doubleTransposition_zero_two, Equiv.Perm.mem_alternatingGroup]⟩, ?_, rfl⟩
  rw [← SetLike.mem_coe]
  rw [alternatingGroup.coe_kleinFour_of_card_eq_four (show Nat.card (Fin 4) = 4 by simp)]
  right
  decide

/-- Helper for Exercise 8-8.2-3: the double transposition swapping `0,3` and `1,2` lies in the
canonical Klein four subgroup of `S₄`. -/
lemma s4_doubleTransposition_zero_three_mem :
    s4_doubleTransposition_zero_three ∈ V4InS4 := by
  refine Subgroup.mem_map.2 ?_
  refine ⟨⟨s4_doubleTransposition_zero_three, by
      simp [s4_doubleTransposition_zero_three, Equiv.Perm.mem_alternatingGroup]⟩, ?_, rfl⟩
  rw [← SetLike.mem_coe]
  rw [alternatingGroup.coe_kleinFour_of_card_eq_four (show Nat.card (Fin 4) = 4 by simp)]
  right
  decide

/-- Helper for Exercise 8-8.2-3: the canonical Klein four subgroup acts transitively on the four
letters. -/
lemma s4_klein_four_orbit_three_eq_univ :
    MulAction.orbit V4InS4 (3 : Fin 4) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  -- The three nontrivial double transpositions send `3` to the other three letters.
  fin_cases x
  · rw [MulAction.mem_orbit_iff]
    refine ⟨⟨s4_doubleTransposition_zero_three, s4_doubleTransposition_zero_three_mem⟩, ?_⟩
    decide
  · rw [MulAction.mem_orbit_iff]
    refine ⟨⟨s4_doubleTransposition_zero_two, s4_doubleTransposition_zero_two_mem⟩, ?_⟩
    decide
  · rw [MulAction.mem_orbit_iff]
    refine ⟨⟨s4_doubleTransposition_zero_one, s4_doubleTransposition_zero_one_mem⟩, ?_⟩
    decide
  · rw [MulAction.mem_orbit_iff]
    exact ⟨1, by simp⟩

-- Proof sketch: use the canonical normal Klein four subgroup `V4 ≤ A₄` together with a cyclic
-- complement of order `3`. The canonical external semidirect-product equivalence is then the
-- derived bridge `SemidirectProduct.mulEquivSubgroup`.
/-- Exercise 8-8.2-3 (3): `A₄` is the semidirect product of its canonical Klein four subgroup `V4`
by a complementary subgroup of order `3`. -/
theorem a4_hasAbelianSemidirectDecomposition :
    ∃ H : Subgroup A4,
      (V4).IsComplement' H ∧
        Nat.card H = 3 := by
  have hV4Normal : (V4).Normal := by infer_instance
  have hcardV4 : Nat.card V4 = 4 := by
    simpa using alternatingGroup.kleinFour_card_of_card_eq_four (show Nat.card (Fin 4) = 4 by simp)
  have hindex : (V4).index = 3 := by
    have hmul : 12 = (V4).index * 4 := by
      simpa [Subgroup.index,
        alternatingGroup.card_of_card_eq_four (show Nat.card (Fin 4) = 4 by simp),
        alternatingGroup.kleinFour_card_of_card_eq_four
          (show Nat.card (Fin 4) = 4 by simp)] using
        (Subgroup.card_eq_card_quotient_mul_card_subgroup V4)
    omega
  have hcoprime : Nat.Coprime (Nat.card V4) (V4).index := by
    rw [hcardV4, hindex]
    decide
  let H : Subgroup A4 :=
    Classical.choose <|
      Subgroup.exists_right_complement'_of_coprime (N := V4) hcoprime
  have hcomp : (V4).IsComplement' H :=
    Classical.choose_spec <|
      Subgroup.exists_right_complement'_of_coprime (N := V4) hcoprime
  refine ⟨H, hcomp, ?_⟩
  -- Cardinal arithmetic recovers that the complement has order `3`.
  have hmul : Nat.card V4 * Nat.card H = Nat.card A4 := hcomp.card_mul
  have hA4 : Nat.card A4 = 12 := by
    simpa using alternatingGroup.card_of_card_eq_four (show Nat.card (Fin 4) = 4 by simp)
  rw [hcardV4, hA4] at hmul
  omega

/- In `S₄`, the double-transposition Klein four subgroup is the image of the canonical owner
`V4 ≤ A₄` under the inclusion `A₄ ↪ S₄`. -/
-- Proof sketch: transport the normality of the canonical Klein four subgroup `V4 ≤ A₄` across the
-- inclusion `A₄ ↪ S₄`, or equivalently identify this subgroup with the normal subgroup of double
-- transpositions in `S₄`.
/-- Exercise 8-8.2-3 (4): the canonical Klein four subgroup of double transpositions in `S₄` is
normal. -/
theorem s4DoubleTranspositionKleinFour_normal :
    (V4InS4).Normal := by
  let hchar : (V4).Characteristic :=
    alternatingGroup.characteristic_kleinFour (show Nat.card (Fin 4) = 4 by simp)
  refine ⟨?_⟩
  intro x hx g
  -- Conjugation by an element of `S₄` induces an automorphism of `A₄`, and characteristicity of
  -- `V4` inside `A₄` keeps the image inside `V4`.
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
  let φ : A4 ≃* A4 := MulAut.conjNormal (H := A4) g
  have hmap : Subgroup.map φ.toMonoidHom V4 = V4 :=
    (Subgroup.characteristic_iff_map_eq.mp hchar) φ
  have hφa : φ a ∈ V4 := by
    rw [← hmap]
    exact Subgroup.mem_map.2 ⟨a, ha, rfl⟩
  refine Subgroup.mem_map.2 ⟨φ a, hφa, ?_⟩
  ext
  simp [φ, MulAut.conjNormal_apply, mul_assoc]

-- Proof sketch: choose a complementary subgroup generated by a `3`-cycle outside the Klein four
-- subgroup and identify it with `S₃`. Together with part `(4)`, this yields the canonical
-- semidirect-product bridge `SemidirectProduct.mulEquivSubgroup`.
/-- Exercise 8-8.2-3 (5): the canonical Klein four subgroup of double transpositions in `S₄`
admits a complementary subgroup isomorphic to `S₃`. -/
theorem s4_hasSemidirectDecomposition :
    ∃ (H : Subgroup S4) (e : H ≃* Perm (Fin 3)), (V4InS4).IsComplement' H := by
  let H : Subgroup S4 := MulAction.stabilizer S4 (3 : Fin 4)
  let e : H ≃* Perm (Fin 3) :=
    s4_stabilizer_three_mulEquiv_subtype_perm.trans s4_subtype_perm_mulEquiv_s3
  have hcomp : (V4InS4).IsComplement' H := by
    refine Subgroup.isComplement'_stabilizer (H := V4InS4) (a := (3 : Fin 4)) ?_ ?_
    · intro h hh
      -- Since the `V4`-action on four letters is transitive and the subgroup has order `4`,
      -- the stabilizer of one point is trivial.
      let _ : Fintype ↥V4InS4 := Fintype.ofFinite _
      let _ : Fintype ↥(MulAction.orbit V4InS4 (3 : Fin 4)) := Fintype.ofFinite _
      let _ : Fintype ↥(MulAction.stabilizer V4InS4 (3 : Fin 4)) := Fintype.ofFinite _
      have hcard : Fintype.card V4InS4 = 4 := by
        rw [← Nat.card_eq_fintype_card]
        have hmap : Nat.card V4InS4 = Nat.card V4 :=
          Nat.card_congr
            (Subgroup.equivMapOfInjective V4 (Subgroup.subtype A4)
              (Subgroup.subtype_injective _)).toEquiv.symm
        rw [hmap]
        simpa using
          alternatingGroup.kleinFour_card_of_card_eq_four (show Nat.card (Fin 4) = 4 by simp)
      have horbit : Fintype.card (MulAction.orbit V4InS4 (3 : Fin 4)) = 4 := by
        simp [s4_klein_four_orbit_three_eq_univ]
      have hmul :=
        MulAction.card_orbit_mul_card_stabilizer_eq_card_group
          (α := ↥V4InS4) (β := Fin 4) (3 : Fin 4)
      have hstab : Fintype.card (MulAction.stabilizer V4InS4 (3 : Fin 4)) = 1 := by
        have hmul' : 4 * Fintype.card (MulAction.stabilizer V4InS4 (3 : Fin 4)) = 4 * 1 := by
          simpa [hcard, horbit, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul
        exact Nat.eq_of_mul_eq_mul_left (by decide) hmul'
      rcases Fintype.card_eq_one_iff.mp hstab with ⟨u, hu⟩
      have hu1 : u = 1 := (hu 1).symm
      have hhu : (⟨h, hh⟩ : MulAction.stabilizer V4InS4 (3 : Fin 4)) = 1 := by
        simpa [hu1] using hu ⟨h, hh⟩
      exact Subtype.ext_iff.mp hhu
    · intro g
      -- Transitivity of the `V4`-action lets us move `g • 3` back to `3`.
      have hgmem : g • (3 : Fin 4) ∈ MulAction.orbit V4InS4 (3 : Fin 4) := by
        simp [s4_klein_four_orbit_three_eq_univ]
      rw [MulAction.mem_orbit_iff] at hgmem
      obtain ⟨k, hk⟩ := hgmem
      refine ⟨k⁻¹, ?_⟩
      calc
        k⁻¹ • g • (3 : Fin 4) = k⁻¹ • (k • (3 : Fin 4)) := by simp [hk]
        _ = 3 := by simp
  exact ⟨H, e, hcomp⟩
