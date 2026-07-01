import Mathlib
import Mathlib.RepresentationTheory.Maschke
import Serre.Chap01.Definition_1_1_4_1
import Serre.Chap02.Theorem_2_2_6_1

-- Declarations for this item will be appended below by the statement pipeline.

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
