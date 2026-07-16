import LinearRepresentations_Serre_1977.Serre.Chap17.Theorem_17_17_6_1.FixedConstituentLiftSelection

universe u v w x

open scoped MonoidAlgebra TensorProduct

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
private noncomputable instance theorem171761TargetModule : Module A V :=
  Module.compHom V (algebraMap A k)
private instance theorem171761TargetScalarTower : IsScalarTower A k V :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

/-- Helper for Theorem 17-17.6-1: a fixed constituent inherits the group-algebra action attached
to its restricted representation. -/
private noncomputable instance fixedConstituentSubmoduleGroupAlgebraModule
    (I : Subgroup G)
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype)) :
    Module (MonoidAlgebra k I) Sbar.toSubmodule :=
  Module.compHom Sbar.toSubmodule Sbar.toRepresentation.asAlgebraHom.toRingHom

/-- Helper for Theorem 17-17.6-1: the inherited group-algebra action on a fixed constituent
extends the scalar action from the residue field. -/
private instance fixedConstituentSubmoduleGroupAlgebraScalarTower
    (I : Subgroup G)
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype)) :
    IsScalarTower k (MonoidAlgebra k I) Sbar.toSubmodule :=
  IsScalarTower.of_algebraMap_smul fun a x ↦ by
    change Sbar.toRepresentation.asAlgebraHom (algebraMap k (MonoidAlgebra k I) a) x = a • x
    simpa [Algebra.smul_def] using
      LinearMap.congr_fun (Sbar.toRepresentation.asAlgebraHom.commutes a) x

/-- Helper for Theorem 17-17.6-1: reduced equivariant endomorphisms of a fixed constituent are
viewed as an `A`-algebra through the residue map. -/
private noncomputable instance fixedConstituentReducedEndAlgebra
    (I : Subgroup G)
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype)) :
    Algebra A (Sbar.toRepresentation.IntertwiningMap Sbar.toRepresentation) :=
  Algebra.compHom (Sbar.toRepresentation.IntertwiningMap Sbar.toRepresentation) (algebraMap A k)

/-- Helper for Theorem 17-17.6-1: the scalar action on reduced equivariant endomorphisms agrees
with the residue-field scalar action. -/
private instance fixedConstituentReducedEndScalarTower
    (I : Subgroup G)
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype)) :
    IsScalarTower A k (Sbar.toRepresentation.IntertwiningMap Sbar.toRepresentation) :=
  IsScalarTower.of_algebraMap_smul fun a f ↦ by
    ext x
    rfl

/-- Helper for Theorem 17-17.6-1: scalar restriction along an algebra map gives the expected
scalar tower on a module. -/
theorem moduleCompHomIsScalarTower
    {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
    {M : Type*} [AddCommMonoid M] [Module S M] :
    letI : Module R M := Module.compHom M (algebraMap R S)
    IsScalarTower R S M := by
  letI : Module R M := Module.compHom M (algebraMap R S)
  exact IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

/-- Helper for Theorem 17-17.6-1: scalar restriction along an algebra map makes the two scalar
actions commute on a module. -/
theorem moduleCompHomSMulCommClass
    {R S : Type*} [CommSemiring R] [Semiring S] [Algebra R S]
    {M : Type*} [AddCommMonoid M] [Module S M] :
    letI : Module R M := Module.compHom M (algebraMap R S)
    SMulCommClass S R M := by
  letI : Module R M := Module.compHom M (algebraMap R S)
  constructor
  intro s r x
  change s • ((algebraMap R S r) • x) = (algebraMap R S r) • (s • x)
  rw [← mul_smul, ← mul_smul, Algebra.commutes]

/-- Helper for Theorem 17-17.6-1: a module over an algebra has commuting scalar actions from
the algebra and its commutative base. -/
theorem algebraModuleSMulCommClass
    {R S : Type*} [CommSemiring R] [Semiring S] [Algebra R S]
    {M : Type*} [AddCommMonoid M] [Module R M] [Module S M] [IsScalarTower R S M] :
    SMulCommClass S R M := by
  constructor
  intro s r x
  rw [← IsScalarTower.algebraMap_smul S r x]
  rw [← IsScalarTower.algebraMap_smul S r (s • x)]
  rw [← mul_smul, ← mul_smul, Algebra.commutes]

/-- Helper for Theorem 17-17.6-1: the carrier of a representation carries the group-algebra
module structure induced by the representation action. -/
noncomputable def representationCarrierGroupAlgebraModule
    {Rg : Type u} [CommRing Rg]
    {H : Type v} [Group H]
    {M : Type w} [AddCommGroup M] [Module Rg M]
    (ρ : Representation Rg H M) :
    Module Rg[H] M :=
  Module.compHom M ρ.asAlgebraHom.toRingHom

/-- Helper for Theorem 17-17.6-1: the representation-induced group-algebra action extends the
base scalar action. -/
theorem representationCarrierGroupAlgebraIsScalarTower
    {Rg : Type u} [CommRing Rg]
    {H : Type v} [Group H]
    {M : Type w} [AddCommGroup M] [Module Rg M]
    (ρ : Representation Rg H M) :
    letI : Module Rg[H] M := representationCarrierGroupAlgebraModule ρ
    IsScalarTower Rg Rg[H] M := by
  letI : Module Rg[H] M := representationCarrierGroupAlgebraModule ρ
  exact IsScalarTower.of_algebraMap_smul fun a x ↦ by
    change ρ.asAlgebraHom (algebraMap Rg Rg[H] a) x = a • x
    simpa [Algebra.smul_def] using LinearMap.congr_fun (ρ.asAlgebraHom.commutes a) x

/-- Helper for Theorem 17-17.6-1: the canonical `asModule` owner of a representation is
group-algebra-linearly equivalent to the original carrier with the representation-induced action. -/
theorem existsRepresentationAsModuleLinearEquiv
    {Rg : Type u} [CommRing Rg]
    {H : Type v} [Group H]
    {M : Type w} [AddCommGroup M] [Module Rg M]
    (ρ : Representation Rg H M) :
    letI : Module Rg[H] M := representationCarrierGroupAlgebraModule ρ
    ∃ e : ρ.asModule ≃ₗ[Rg[H]] M, ∀ x, e x = ρ.asModuleEquiv x := by
  letI : Module Rg[H] M := representationCarrierGroupAlgebraModule ρ
  let toLinear : ρ.asModule →ₗ[Rg[H]] M :=
    { toFun := fun x ↦ ρ.asModuleEquiv x
      map_add' := by
        intro x y
        rfl
      map_smul' := by
        intro r x
        calc
          ρ.asModuleEquiv (r • x) = ρ.asAlgebraHom r (ρ.asModuleEquiv x) :=
            ρ.asModuleEquiv_map_smul r x
          _ = r • ρ.asModuleEquiv x := rfl }
  let invLinear : M →ₗ[Rg[H]] ρ.asModule :=
    { toFun := fun x ↦ ρ.asModuleEquiv.symm x
      map_add' := by
        intro x y
        apply ρ.asModuleEquiv.injective
        simp
      map_smul' := by
        intro r x
        apply ρ.asModuleEquiv.injective
        calc
          ρ.asModuleEquiv (ρ.asModuleEquiv.symm (r • x)) = r • x := by
            simp
          _ = ρ.asAlgebraHom r x := rfl
          _ = ρ.asModuleEquiv (r • ρ.asModuleEquiv.symm x) := by
            rw [ρ.asModuleEquiv_map_smul]
            simp }
  refine ⟨LinearEquiv.ofLinear toLinear invLinear ?_ ?_, ?_⟩
  · ext x
    rfl
  · ext x
    simp [toLinear, invLinear]
  · intro x
    rfl

/-- Helper for Theorem 17-17.6-1: the canonical `asModule` owner of a representation is
identified with the original carrier. -/
noncomputable def representationAsModuleLinearEquiv
    {Rg : Type u} [CommRing Rg]
    {H : Type v} [Group H]
    {M : Type w} [AddCommGroup M] [Module Rg M]
    (ρ : Representation Rg H M) :
    letI : Module Rg[H] M := representationCarrierGroupAlgebraModule ρ
    ρ.asModule ≃ₗ[Rg[H]] M :=
  letI : Module Rg[H] M := representationCarrierGroupAlgebraModule ρ
  Classical.choose (existsRepresentationAsModuleLinearEquiv ρ)

/-- Helper for Theorem 17-17.6-1: the carrier identification for a representation acts as the
canonical `asModuleEquiv` on vectors. -/
theorem representationAsModuleLinearEquiv_apply
    {Rg : Type u} [CommRing Rg]
    {H : Type v} [Group H]
    {M : Type w} [AddCommGroup M] [Module Rg M]
    (ρ : Representation Rg H M) (x : ρ.asModule) :
    letI : Module Rg[H] M := representationCarrierGroupAlgebraModule ρ
    representationAsModuleLinearEquiv ρ x = ρ.asModuleEquiv x := by
  letI : Module Rg[H] M := representationCarrierGroupAlgebraModule ρ
  exact Classical.choose_spec (existsRepresentationAsModuleLinearEquiv ρ) x

/-- Helper for Theorem 17-17.6-1: the inverse carrier identification for a representation acts as
the inverse of `asModuleEquiv` on vectors. -/
theorem representationAsModuleLinearEquiv_symm_apply
    {Rg : Type u} [CommRing Rg]
    {H : Type v} [Group H]
    {M : Type w} [AddCommGroup M] [Module Rg M]
    (ρ : Representation Rg H M) (x : M) :
    letI : Module Rg[H] M := representationCarrierGroupAlgebraModule ρ
    (representationAsModuleLinearEquiv ρ).symm x = ρ.asModuleEquiv.symm x := by
  letI : Module Rg[H] M := representationCarrierGroupAlgebraModule ρ
  apply (representationAsModuleLinearEquiv ρ).injective
  rw [LinearEquiv.apply_symm_apply]
  simp [representationAsModuleLinearEquiv_apply]

/-- Helper for Theorem 17-17.6-1: equivariant endomorphisms of a representation identify with
endomorphisms of the carrier as a module over the group algebra. -/
noncomputable def representationEquivAlgEnd
    {Rg : Type u} [CommRing Rg]
    {H : Type v} [Group H]
    {M : Type w} [AddCommGroup M] [Module Rg M]
    (ρ : Representation Rg H M) :
    letI : Module Rg[H] M := representationCarrierGroupAlgebraModule ρ
    letI : IsScalarTower Rg Rg[H] M := representationCarrierGroupAlgebraIsScalarTower ρ
    letI : SMulCommClass Rg[H] Rg M := algebraModuleSMulCommClass (R := Rg) (S := Rg[H]) (M := M)
    ρ.IntertwiningMap ρ ≃ₐ[Rg] Module.End Rg[H] M :=
  letI : Module Rg[H] M := representationCarrierGroupAlgebraModule ρ
  letI : IsScalarTower Rg Rg[H] M := representationCarrierGroupAlgebraIsScalarTower ρ
  letI : SMulCommClass Rg[H] Rg M := algebraModuleSMulCommClass (R := Rg) (S := Rg[H]) (M := M)
  letI : Algebra Rg (Module.End Rg[H] M) := Module.End.instAlgebra Rg Rg[H] M
  (Representation.IntertwiningMap.equivAlgEnd (ρ := ρ)).trans
    (LinearEquiv.conjAlgEquiv Rg (representationAsModuleLinearEquiv ρ))

/-- Helper for Theorem 17-17.6-1: the group-algebra endomorphism associated to an equivariant
endomorphism acts by the same formula on the carrier. -/
theorem representationEquivAlgEnd_apply_apply
    {Rg : Type u} [CommRing Rg]
    {H : Type v} [Group H]
    {M : Type w} [AddCommGroup M] [Module Rg M]
    (ρ : Representation Rg H M)
    (u : ρ.IntertwiningMap ρ) (x : M) :
    letI : Module Rg[H] M := representationCarrierGroupAlgebraModule ρ
    letI : IsScalarTower Rg Rg[H] M := representationCarrierGroupAlgebraIsScalarTower ρ
    letI : SMulCommClass Rg[H] Rg M := algebraModuleSMulCommClass (R := Rg) (S := Rg[H]) (M := M)
    representationEquivAlgEnd ρ u x = u x := by
  letI : Module Rg[H] M := representationCarrierGroupAlgebraModule ρ
  letI : IsScalarTower Rg Rg[H] M := representationCarrierGroupAlgebraIsScalarTower ρ
  letI : SMulCommClass Rg[H] Rg M := algebraModuleSMulCommClass (R := Rg) (S := Rg[H]) (M := M)
  letI : Algebra Rg (Module.End Rg[H] M) := Module.End.instAlgebra Rg Rg[H] M
  simp [representationEquivAlgEnd, LinearEquiv.conjAlgEquiv_apply,
    Representation.IntertwiningMap.equivAlgEnd,
    Representation.IntertwiningMap.equivLinearMapAsModule,
    representationAsModuleLinearEquiv_apply,
    representationAsModuleLinearEquiv_symm_apply]
  change u (ρ.asModuleEquiv.symm x) = u x
  rfl

/-- Helper for Theorem 17-17.6-1: the inverse group-algebra endomorphism identification also acts
by the same formula on the carrier. -/
theorem representationEquivAlgEnd_symm_apply_apply
    {Rg : Type u} [CommRing Rg]
    {H : Type v} [Group H]
    {M : Type w} [AddCommGroup M] [Module Rg M]
    (ρ : Representation Rg H M)
    (u :
      letI : Module Rg[H] M := representationCarrierGroupAlgebraModule ρ
      letI : IsScalarTower Rg Rg[H] M := representationCarrierGroupAlgebraIsScalarTower ρ
      letI : SMulCommClass Rg[H] Rg M :=
        algebraModuleSMulCommClass (R := Rg) (S := Rg[H]) (M := M)
      Module.End Rg[H] M)
    (x : M) :
    letI : Module Rg[H] M := representationCarrierGroupAlgebraModule ρ
    letI : IsScalarTower Rg Rg[H] M := representationCarrierGroupAlgebraIsScalarTower ρ
    letI : SMulCommClass Rg[H] Rg M := algebraModuleSMulCommClass (R := Rg) (S := Rg[H]) (M := M)
    (representationEquivAlgEnd ρ).symm u x = u x := by
  letI : Module Rg[H] M := representationCarrierGroupAlgebraModule ρ
  letI : IsScalarTower Rg Rg[H] M := representationCarrierGroupAlgebraIsScalarTower ρ
  letI : SMulCommClass Rg[H] Rg M := algebraModuleSMulCommClass (R := Rg) (S := Rg[H]) (M := M)
  letI : Algebra Rg (Module.End Rg[H] M) := Module.End.instAlgebra Rg Rg[H] M
  have h :=
    congrArg (fun f : Module.End Rg[H] M ↦ f x)
      ((representationEquivAlgEnd ρ).apply_symm_apply u)
  change (representationEquivAlgEnd ρ ((representationEquivAlgEnd ρ).symm u)) x = u x at h
  rw [representationEquivAlgEnd_apply_apply] at h
  exact h

/-- Helper for Theorem 17-17.6-1: the inverse `ofModule'` endomorphism identification acts by
the same formula on the carrier. -/
theorem ofModule'_equivAlgEnd_symm_apply_apply
    {Rg : Type u} [CommRing Rg]
    {H : Type v} [Group H]
    {M : Type w} [AddCommGroup M] [Module Rg M] [Module Rg[H] M]
    [IsScalarTower Rg Rg[H] M]
    (u : Module.End Rg[H] M) (x : M) :
    (ofModule'_equivAlgEnd (G := H) Rg M).symm u x = u x := by
  have h :=
    congrArg (fun f : Module.End Rg[H] M ↦ f x)
      ((ofModule'_equivAlgEnd (G := H) Rg M).apply_symm_apply u)
  change ofModule'_equivAlgEnd (G := H) Rg M
      ((ofModule'_equivAlgEnd (G := H) Rg M).symm u) x = u x at h
  rw [ofModule'_equivAlgEnd_apply_apply] at h
  exact h

/-- Helper for Theorem 17-17.6-1: a representation and its induced `ofModule'` owner have the
same equivariant endomorphism algebra. -/
noncomputable def representationEquivOfModuleEndAlgEquiv
    {Rg : Type u} [CommRing Rg]
    {H : Type v} [Group H]
    {M : Type w} [AddCommGroup M] [Module Rg M]
    (ρ : Representation Rg H M) :
    letI : Module Rg[H] M := representationCarrierGroupAlgebraModule ρ
    letI : IsScalarTower Rg Rg[H] M := representationCarrierGroupAlgebraIsScalarTower ρ
    letI : SMulCommClass Rg[H] Rg M := algebraModuleSMulCommClass (R := Rg) (S := Rg[H]) (M := M)
    ρ.IntertwiningMap ρ ≃ₐ[Rg]
      (Representation.ofModule' M : Representation Rg H M).IntertwiningMap
        (Representation.ofModule' M : Representation Rg H M) := by
  letI : Module Rg[H] M := representationCarrierGroupAlgebraModule ρ
  letI : IsScalarTower Rg Rg[H] M := representationCarrierGroupAlgebraIsScalarTower ρ
  letI : SMulCommClass Rg[H] Rg M := algebraModuleSMulCommClass (R := Rg) (S := Rg[H]) (M := M)
  letI : Algebra Rg (Module.End Rg[H] M) := Module.End.instAlgebra Rg Rg[H] M
  exact (representationEquivAlgEnd ρ).trans (ofModule'_equivAlgEnd (G := H) Rg M).symm

/-- Helper for Theorem 17-17.6-1: transporting an endomorphism to the `ofModule'` owner does not
change its action on the carrier. -/
theorem representationEquivOfModuleEndAlgEquiv_apply_apply
    {Rg : Type u} [CommRing Rg]
    {H : Type v} [Group H]
    {M : Type w} [AddCommGroup M] [Module Rg M]
    (ρ : Representation Rg H M)
    (u : ρ.IntertwiningMap ρ) (x : M) :
    letI : Module Rg[H] M := representationCarrierGroupAlgebraModule ρ
    letI : IsScalarTower Rg Rg[H] M := representationCarrierGroupAlgebraIsScalarTower ρ
    letI : SMulCommClass Rg[H] Rg M := algebraModuleSMulCommClass (R := Rg) (S := Rg[H]) (M := M)
    representationEquivOfModuleEndAlgEquiv ρ u x = u x := by
  letI : Module Rg[H] M := representationCarrierGroupAlgebraModule ρ
  letI : IsScalarTower Rg Rg[H] M := representationCarrierGroupAlgebraIsScalarTower ρ
  letI : SMulCommClass Rg[H] Rg M := algebraModuleSMulCommClass (R := Rg) (S := Rg[H]) (M := M)
  letI : Algebra Rg (Module.End Rg[H] M) := Module.End.instAlgebra Rg Rg[H] M
  calc
    representationEquivOfModuleEndAlgEquiv ρ u x =
        (representationEquivAlgEnd ρ u) x := by
          exact ofModule'_equivAlgEnd_symm_apply_apply
            (Rg := Rg) (H := H) (M := M) (representationEquivAlgEnd ρ u) x
    _ = u x := by
          exact representationEquivAlgEnd_apply_apply ρ u x

/-- Helper for Theorem 17-17.6-1: transporting back from the `ofModule'` owner does not change
the action on the carrier. -/
theorem representationEquivOfModuleEndAlgEquiv_symm_apply_apply
    {Rg : Type u} [CommRing Rg]
    {H : Type v} [Group H]
    {M : Type w} [AddCommGroup M] [Module Rg M]
    (ρ : Representation Rg H M)
    (u :
      letI : Module Rg[H] M := representationCarrierGroupAlgebraModule ρ
      letI : IsScalarTower Rg Rg[H] M := representationCarrierGroupAlgebraIsScalarTower ρ
      letI : SMulCommClass Rg[H] Rg M :=
        algebraModuleSMulCommClass (R := Rg) (S := Rg[H]) (M := M)
      (Representation.ofModule' M : Representation Rg H M).IntertwiningMap
        (Representation.ofModule' M : Representation Rg H M))
    (x : M) :
    letI : Module Rg[H] M := representationCarrierGroupAlgebraModule ρ
    letI : IsScalarTower Rg Rg[H] M := representationCarrierGroupAlgebraIsScalarTower ρ
    letI : SMulCommClass Rg[H] Rg M := algebraModuleSMulCommClass (R := Rg) (S := Rg[H]) (M := M)
    (representationEquivOfModuleEndAlgEquiv ρ).symm u x = u x := by
  letI : Module Rg[H] M := representationCarrierGroupAlgebraModule ρ
  letI : IsScalarTower Rg Rg[H] M := representationCarrierGroupAlgebraIsScalarTower ρ
  letI : SMulCommClass Rg[H] Rg M := algebraModuleSMulCommClass (R := Rg) (S := Rg[H]) (M := M)
  letI : Algebra Rg (Module.End Rg[H] M) := Module.End.instAlgebra Rg Rg[H] M
  have h :=
    representationEquivOfModuleEndAlgEquiv_apply_apply ρ
      ((representationEquivOfModuleEndAlgEquiv ρ).symm u) x
  rw [(representationEquivOfModuleEndAlgEquiv ρ).apply_symm_apply] at h
  exact h.symm

/-- Helper for Theorem 17-17.6-1: endomorphisms of a residue-field representation carry the
restricted `A`-algebra structure through the residue map. -/
noncomputable def reducedRepresentationEndAlgebra
    {R : Type u} [CommRing R] [IsLocalRing R]
    {H : Type v} [Group H]
    {M : Type w} [AddCommGroup M] [Module (IsLocalRing.ResidueField R) M]
    (ρ : Representation (IsLocalRing.ResidueField R) H M) :
    Algebra R (ρ.IntertwiningMap ρ) :=
  Algebra.compHom (ρ.IntertwiningMap ρ) (algebraMap R (IsLocalRing.ResidueField R))

/-- Helper for Theorem 17-17.6-1: the restricted `A`-algebra structure on reduced equivariant
endomorphisms is compatible with the residue-field scalar action. -/
theorem reducedRepresentationEndScalarTower
    {R : Type u} [CommRing R] [IsLocalRing R]
    {H : Type v} [Group H]
    {M : Type w} [AddCommGroup M] [Module (IsLocalRing.ResidueField R) M]
    (ρ : Representation (IsLocalRing.ResidueField R) H M) :
    letI : Algebra R (ρ.IntertwiningMap ρ) := reducedRepresentationEndAlgebra ρ
    IsScalarTower R (IsLocalRing.ResidueField R) (ρ.IntertwiningMap ρ) := by
  letI : Algebra R (ρ.IntertwiningMap ρ) := reducedRepresentationEndAlgebra ρ
  exact IsScalarTower.of_algebraMap_smul fun _ _ ↦ by
    ext x
    rfl

/-- Helper for Theorem 17-17.6-1: Serre's literal source object `G₁` is the total space of the
transport fibers `U_s`, i.e. pairs `(s, u)` with `u : U_s`. Naming the carrier now keeps the
remaining finite-cover work focused on the group law and determinant normalization. -/
abbrev fixed_constituent_transport_total_space
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S) : Type (max u v x) :=
  Σ s : G, fixed_constituent_transport_fiber (A := A) (G := G) I ρA_I s

/-- Helper for Theorem 17-17.6-1: the literal source projection `G₁ → G` forgets the transport
operator and remembers only the group element `s`. -/
abbrev fixed_constituent_transport_total_space_proj
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S) :
    fixed_constituent_transport_total_space (A := A) (G := G) I ρA_I → G :=
  Sigma.fst

/-- Helper for Theorem 17-17.6-1: the chosen lifted transport automorphisms give a set-theoretic
section of Serre's projection `G₁ → G`. This is the exact source-faithful choice of one element
in each nonempty fiber `U_s`. -/
noncomputable def fixed_constituent_transport_total_space_section
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S)) :
    G → fixed_constituent_transport_total_space (A := A) (G := G) I ρA_I :=
  fun s ↦
    ⟨s,
      fixed_constituent_transport_aut_of_lift
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s⟩

/-- Helper for Theorem 17-17.6-1: Serre's projection `G₁ → G` is surjective because each fiber
`U_s` is inhabited by the chosen lifted transport automorphism. -/
theorem fixed_constituent_transport_total_space_proj_surjective
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S)) :
    Function.Surjective
      (fixed_constituent_transport_total_space_proj
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)) := by
  intro s
  -- Use the chosen point of the fiber `U_s` as the preimage of `s`.
  refine
    ⟨fixed_constituent_transport_total_space_section
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s, rfl⟩

/-- Helper for Theorem 17-17.6-1: Serre's transport fibers compose directly on the literal lifted
constituent carrier. This is the source-faithful multiplication rule on the intermediate total
space `G₁ = Σ s, U_s` before any determinant normalization. -/
noncomputable def fixed_constituent_transport_fiber_comp
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    {s t : G}
    (u :
      fixed_constituent_transport_fiber
        (A := A) (G := G) I ρA_I s)
    (v :
      fixed_constituent_transport_fiber
        (A := A) (G := G) I ρA_I t) :
    fixed_constituent_transport_fiber
      (A := A) (G := G) I ρA_I (s * t) := by
  let v_over_s :
      Representation.Equiv
        (ρA_I.comp (MulAut.conjNormal (s * t)⁻¹).toMonoidHom)
        (ρA_I.comp (MulAut.conjNormal s⁻¹).toMonoidHom) := by
    -- Reuse the same linear transport operator `v`, but now view it after conjugating the source
    -- action by `s`; this is Serre's literal composition law on the transport fibers `U_s`.
    refine Representation.Equiv.mk v.toLinearEquiv ?_
    intro a
    ext x
    simpa [MulAut.conjNormal_apply, mul_assoc] using
      LinearMap.congr_fun (v.isIntertwining' ((MulAut.conjNormal s⁻¹) a)) x
  -- Compose the `t`-transport over `s` with the `s`-transport to land in the `(s * t)`-fiber.
  exact v_over_s.trans u

/-- Helper for Theorem 17-17.6-1: the identity transport belongs to the fiber `U_1`. This gives
the neutral element on Serre's literal total space `G₁`. -/
noncomputable def fixed_constituent_transport_fiber_one
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S) :
    fixed_constituent_transport_fiber
      (A := A) (G := G) I ρA_I (1 : G) := by
  refine Representation.Equiv.mk (LinearEquiv.refl A P_S) ?_
  intro a
  ext x
  simp

/-- Helper for Theorem 17-17.6-1: an element of the kernel fiber `U₁` is literally an
`A[I]`-equivariant endomorphism of the fixed lift `ρA_I`. This is the source-faithful bridge from
Serre's kernel notation to the owner endomorphism space used by the Chapter `14` reduction API. -/
theorem fixed_constituent_transport_kernel_isIntertwiningMap
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (u :
      fixed_constituent_transport_fiber
        (A := A) (G := G) I ρA_I (1 : G)) :
    ρA_I.IsIntertwiningMap ρA_I u.toLinearMap := by
  -- At `s = 1`, the conjugated source action is definitionally the original `I`-action.
  refine Representation.IsIntertwiningMap.mk ?_
  intro a x
  simpa [fixed_constituent_transport_fiber, MulAut.conjNormal_apply, mul_assoc] using
    LinearMap.congr_fun (u.isIntertwining' a) x

/-- Helper for Theorem 17-17.6-1: repackage a kernel element `u ∈ U₁` as an actual element of the
equivariant endomorphism module `End_{A[I]}(P_S)`. -/
noncomputable def fixed_constituent_transport_kernel_intertwiningEnd
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (u :
      fixed_constituent_transport_fiber
        (A := A) (G := G) I ρA_I (1 : G)) :
    ρA_I.IntertwiningMap ρA_I :=
  u.toLinearMap.intertwiningMap_of_isIntertwiningMap
    ρA_I ρA_I
    (fixed_constituent_transport_kernel_isIntertwiningMap
      (A := A) (G := G) (I := I) ρA_I u).isIntertwining

/-- Helper for Theorem 17-17.6-1: Schur's lemma on the reduced fixed constituent says that every
`k[I]`-equivariant endomorphism of `S̄` is scalar. This is Serre's reduced-side input before the
scalar line is lifted back across the fixed projective cover. -/
theorem fixed_constituent_reduced_scalar_id_surjective
    [IsAlgClosed k]
    (I : Subgroup G)
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    (u : Sbar.toRepresentation.IntertwiningMap Sbar.toRepresentation) :
    ∃ c : k, u = c • Representation.IntertwiningMap.id Sbar.toRepresentation := by
  letI : Sbar.toRepresentation.IsIrreducible := hSbar_irred
  obtain ⟨c, hc⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := Sbar.toRepresentation)).surjective u
  refine ⟨c, ?_⟩
  calc
    u = algebraMap k (Sbar.toRepresentation.IntertwiningMap Sbar.toRepresentation) c := hc.symm
    _ = c • (1 : Sbar.toRepresentation.IntertwiningMap Sbar.toRepresentation) := by simp
    _ = c • Representation.IntertwiningMap.id Sbar.toRepresentation := rfl

/-- Helper for Theorem 17-17.6-1: every `A[I]`-equivariant endomorphism of the fixed lift is a
scalar multiple of the identity. This is Serre's literal bridge from the kernel fiber `U₁` to the
scalar group `Aˣ`. -/
noncomputable def fixed_constituent_endAlgHom
    (I : Subgroup G) [I.Normal]
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S) :
    ρA_I.IntertwiningMap ρA_I →ₐ[A]
      Sbar.toRepresentation.IntertwiningMap Sbar.toRepresentation := by
  letI : Module A[I] P_S := representationCarrierGroupAlgebraModule ρA_I
  letI : IsScalarTower A A[I] P_S := representationCarrierGroupAlgebraIsScalarTower ρA_I
  letI : Module k[I] Sbar.toSubmodule :=
    representationCarrierGroupAlgebraModule Sbar.toRepresentation
  letI : IsScalarTower k k[I] Sbar.toSubmodule :=
    representationCarrierGroupAlgebraIsScalarTower Sbar.toRepresentation
  letI : Module A Sbar.toSubmodule := Module.compHom Sbar.toSubmodule (algebraMap A k)
  letI : IsScalarTower A k Sbar.toSubmodule :=
    moduleCompHomIsScalarTower (R := A) (S := k) (M := Sbar.toSubmodule)
  letI : Algebra A (Sbar.toRepresentation.IntertwiningMap Sbar.toRepresentation) :=
    reducedRepresentationEndAlgebra (R := A) Sbar.toRepresentation
  letI : IsScalarTower A k (Sbar.toRepresentation.IntertwiningMap Sbar.toRepresentation) :=
    reducedRepresentationEndScalarTower (R := A) Sbar.toRepresentation
  letI :
      Algebra A
        ((Representation.ofModule' Sbar.toSubmodule :
            Representation k I Sbar.toSubmodule).IntertwiningMap
          (Representation.ofModule' Sbar.toSubmodule :
            Representation k I Sbar.toSubmodule)) :=
    Algebra.compHom
      ((Representation.ofModule' Sbar.toSubmodule :
          Representation k I Sbar.toSubmodule).IntertwiningMap
        (Representation.ofModule' Sbar.toSubmodule :
          Representation k I Sbar.toSubmodule))
      (algebraMap A k)
  letI :
      IsScalarTower A k
        ((Representation.ofModule' Sbar.toSubmodule :
            Representation k I Sbar.toSubmodule).IntertwiningMap
          (Representation.ofModule' Sbar.toSubmodule :
            Representation k I Sbar.toSubmodule)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ by
      ext x
      rfl
  let hred : red_S.IsResidueFieldReduction I := by
    simpa using hLiftSbar
  exact
    (AlgEquiv.restrictScalars A
      (representationEquivOfModuleEndAlgEquiv Sbar.toRepresentation).symm).toAlgHom.comp <|
      hred.endAlgHom.comp <|
        (representationEquivOfModuleEndAlgEquiv ρA_I).toAlgHom

/-- Helper for Theorem 17-17.6-1: the fixed-constituent endomorphism reduction agrees with
applying the lifted endomorphism before reducing, on the reduction image. -/
theorem fixed_constituent_endAlgHom_comp_apply
    (I : Subgroup G) [I.Normal]
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (u : ρA_I.IntertwiningMap ρA_I) (x : P_S) :
    fixed_constituent_endAlgHom
        (A := A) (G := G) (V := V) (I := I) (ρ := ρ) (Sbar := Sbar)
        ρA_I red_S hLiftSbar u (red_S x) =
      red_S (u x) := by
  letI : Module A[I] P_S := representationCarrierGroupAlgebraModule ρA_I
  letI : IsScalarTower A A[I] P_S := representationCarrierGroupAlgebraIsScalarTower ρA_I
  letI : Module k[I] Sbar.toSubmodule :=
    representationCarrierGroupAlgebraModule Sbar.toRepresentation
  letI : IsScalarTower k k[I] Sbar.toSubmodule :=
    representationCarrierGroupAlgebraIsScalarTower Sbar.toRepresentation
  letI : Module A Sbar.toSubmodule := Module.compHom Sbar.toSubmodule (algebraMap A k)
  letI : IsScalarTower A k Sbar.toSubmodule :=
    moduleCompHomIsScalarTower (R := A) (S := k) (M := Sbar.toSubmodule)
  letI : Algebra A (Sbar.toRepresentation.IntertwiningMap Sbar.toRepresentation) :=
    reducedRepresentationEndAlgebra (R := A) Sbar.toRepresentation
  letI : IsScalarTower A k (Sbar.toRepresentation.IntertwiningMap Sbar.toRepresentation) :=
    reducedRepresentationEndScalarTower (R := A) Sbar.toRepresentation
  letI :
      Algebra A
        ((Representation.ofModule' Sbar.toSubmodule :
            Representation k I Sbar.toSubmodule).IntertwiningMap
          (Representation.ofModule' Sbar.toSubmodule :
            Representation k I Sbar.toSubmodule)) :=
    Algebra.compHom
      ((Representation.ofModule' Sbar.toSubmodule :
          Representation k I Sbar.toSubmodule).IntertwiningMap
        (Representation.ofModule' Sbar.toSubmodule :
          Representation k I Sbar.toSubmodule))
      (algebraMap A k)
  letI :
      IsScalarTower A k
        ((Representation.ofModule' Sbar.toSubmodule :
            Representation k I Sbar.toSubmodule).IntertwiningMap
          (Representation.ofModule' Sbar.toSubmodule :
            Representation k I Sbar.toSubmodule)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ by
      ext x
      rfl
  let hred : red_S.IsResidueFieldReduction I := by
    simpa using hLiftSbar
  let uOfModule := representationEquivOfModuleEndAlgEquiv ρA_I u
  calc
    fixed_constituent_endAlgHom
        (A := A) (G := G) (V := V) (I := I) (ρ := ρ) (Sbar := Sbar)
        ρA_I red_S hLiftSbar u (red_S x) =
      hred.endAlgHom uOfModule (red_S x) := by
        change
          (representationEquivOfModuleEndAlgEquiv Sbar.toRepresentation).symm
              (hred.endAlgHom uOfModule) (red_S x) =
            hred.endAlgHom uOfModule (red_S x)
        exact
          representationEquivOfModuleEndAlgEquiv_symm_apply_apply
            Sbar.toRepresentation (hred.endAlgHom uOfModule) (red_S x)
    _ = red_S (uOfModule x) := by
        exact LinearMap.IsResidueFieldReduction.endAlgHom_comp_apply hred uOfModule x
    _ = red_S (u x) := by
        rw [representationEquivOfModuleEndAlgEquiv_apply_apply]

/-- Helper for Theorem 17-17.6-1: the residue map on `A` induces the monoid hom used by
`Units.map` on determinant scalars. Naming it once keeps later determinant statements from
repeated coercion failures. -/
abbrev residueUnitHom : A →* k :=
  (IsLocalRing.residue A).toMonoidHom

/-- Helper for Theorem 17-17.6-1: every `A[I]`-equivariant endomorphism of the fixed lift is a
scalar multiple of the identity. This is Serre's literal bridge from the kernel fiber `U₁` to the
scalar group `Aˣ`. -/
theorem fixed_constituent_endAlgHom_scalar_id_transport
    (I : Subgroup G) [I.Normal]
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (a : A) :
    fixed_constituent_endAlgHom
        (A := A) (G := G) (V := V) (I := I) (ρ := ρ) (Sbar := Sbar)
        ρA_I red_S hLiftSbar (a • Representation.IntertwiningMap.id ρA_I) =
      (IsLocalRing.residue A a) • Representation.IntertwiningMap.id Sbar.toRepresentation := by
  -- The reduction algebra hom carries Serre's scalar line `A · id` to the reduced scalar line
  -- `k · id` by compatibility with scalar multiplication and the identity.
  letI : Module A[I] P_S := representationCarrierGroupAlgebraModule ρA_I
  letI : IsScalarTower A A[I] P_S := representationCarrierGroupAlgebraIsScalarTower ρA_I
  letI : Module k[I] Sbar.toSubmodule :=
    representationCarrierGroupAlgebraModule Sbar.toRepresentation
  letI : IsScalarTower k k[I] Sbar.toSubmodule :=
    representationCarrierGroupAlgebraIsScalarTower Sbar.toRepresentation
  letI : Algebra A (Sbar.toRepresentation.IntertwiningMap Sbar.toRepresentation) :=
    reducedRepresentationEndAlgebra (R := A) Sbar.toRepresentation
  letI : IsScalarTower A k (Sbar.toRepresentation.IntertwiningMap Sbar.toRepresentation) :=
    reducedRepresentationEndScalarTower (R := A) Sbar.toRepresentation
  apply Representation.IntertwiningMap.ext
  ext y
  let hred : red_S.IsResidueFieldReduction I := by
    simpa using hLiftSbar
  obtain ⟨x, hx⟩ :=
    fixed_constituent_reduction_surjective (A := A) (H := I) hred y
  rw [← hx]
  have hsub :
      (fixed_constituent_endAlgHom
          (A := A) (G := G) (V := V) (I := I) (ρ := ρ) (Sbar := Sbar)
          ρA_I red_S hLiftSbar
          (a • Representation.IntertwiningMap.id ρA_I)).toLinearMap (red_S x) =
        ((IsLocalRing.residue A a) •
          Representation.IntertwiningMap.id Sbar.toRepresentation).toLinearMap (red_S x) := by
    calc
      (fixed_constituent_endAlgHom
          (A := A) (G := G) (V := V) (I := I) (ρ := ρ) (Sbar := Sbar)
          ρA_I red_S hLiftSbar
          (a • Representation.IntertwiningMap.id ρA_I)).toLinearMap (red_S x) =
        red_S ((a • Representation.IntertwiningMap.id ρA_I) x) := by
          change
            fixed_constituent_endAlgHom
                (A := A) (G := G) (V := V) (I := I) (ρ := ρ) (Sbar := Sbar)
                ρA_I red_S hLiftSbar
                (a • Representation.IntertwiningMap.id ρA_I) (red_S x) =
              red_S ((a • Representation.IntertwiningMap.id ρA_I) x)
          exact
            fixed_constituent_endAlgHom_comp_apply
              (A := A) (G := G) (V := V) (I := I) (ρ := ρ) (Sbar := Sbar)
              ρA_I red_S hLiftSbar (a • Representation.IntertwiningMap.id ρA_I) x
      _ = (IsLocalRing.residue A a) • red_S x := by
          calc
            red_S ((a • Representation.IntertwiningMap.id ρA_I) x) =
              red_S (a • x) := by
                rfl
            _ = a • red_S x := by
                exact red_S.map_smul a x
            _ = (IsLocalRing.residue A a) • red_S x := by
                simpa [IsLocalRing.ResidueField.algebraMap_eq] using
                  (IsScalarTower.algebraMap_smul k a (red_S x))
      _ = ((IsLocalRing.residue A a) •
            Representation.IntertwiningMap.id Sbar.toRepresentation).toLinearMap
          (red_S x) := by
          rfl
  exact congrArg Subtype.val hsub

/-- Helper for Theorem 17-17.6-1: the scalar line `A · id` in `End_{A[I]}(P_S)` already maps onto
the whole reduced endomorphism algebra `End_{k[I]}(S̄)`. This is the exact closed-fiber statement
Serre uses before invoking Nakayama on the fixed lift. -/
theorem fixed_constituent_scalar_line_closed_fiber_top
    [IsAlgClosed k]
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S) :
    let N : Submodule A (ρA_I.IntertwiningMap ρA_I) :=
      Submodule.span A ({Representation.IntertwiningMap.id ρA_I} :
        Set (ρA_I.IntertwiningMap ρA_I))
    Submodule.map
      (fixed_constituent_endAlgHom
        (A := A) (G := G) (V := V) (I := I) (ρ := ρ) (Sbar := Sbar)
        ρA_I red_S hLiftSbar).toLinearMap N = ⊤ := by
  let N : Submodule A (ρA_I.IntertwiningMap ρA_I) :=
    Submodule.span A ({Representation.IntertwiningMap.id ρA_I} :
      Set (ρA_I.IntertwiningMap ρA_I))
  rw [eq_top_iff]
  intro ubar hubar
  -- Route correction: the old route stalled on transport wrappers. The source-faithful object is
  -- the scalar line `A · id`, and Serre's reduced Schur lemma already shows its reduction is all
  -- of `End_{k[I]}(S̄)`.
  obtain ⟨c, hc⟩ :=
    fixed_constituent_reduced_scalar_id_surjective
      (A := A) (G := G) (I := I) (ρ := ρ) (Sbar := Sbar) hSbar_irred ubar
  obtain ⟨a, ha⟩ : ∃ a : A, IsLocalRing.residue A a = c :=
    IsLocalRing.residue_surjective c
  refine Submodule.mem_map.mpr ?_
  refine ⟨a • Representation.IntertwiningMap.id ρA_I, ?_, ?_⟩
  · -- We now record that the chosen lift lies on the scalar line `A · id`.
    exact Submodule.mem_span_singleton.2 ⟨a, rfl⟩
  · -- Reducing the lifted scalar identity lands exactly on the prescribed reduced scalar.
    simpa [ha, hc] using
      fixed_constituent_endAlgHom_scalar_id_transport
        (A := A) (G := G) (I := I) (ρ := ρ) (Sbar := Sbar)
        ρA_I red_S hLiftSbar a

/-- Helper for Theorem 17-17.6-1: every `A[I]`-equivariant endomorphism of the fixed lift is a
scalar multiple of the identity. This is Serre's literal bridge from the kernel fiber `U₁` to the
scalar group `Aˣ`. -/
theorem fixed_constituent_lift_equivariant_endomorphism_scalar
    [IsAlgClosed k]
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (u : ρA_I.IntertwiningMap ρA_I) :
    ∃ a : A, u = a • Representation.IntertwiningMap.id ρA_I := by
  letI : Module (MonoidAlgebra A I) P_S := Module.compHom P_S ρA_I.asAlgebraHom.toRingHom
  letI : IsScalarTower A (MonoidAlgebra A I) P_S :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      change ρA_I.asAlgebraHom (algebraMap A (MonoidAlgebra A I) a) x = a • x
      simpa [Algebra.smul_def] using LinearMap.congr_fun (ρA_I.asAlgebraHom.commutes a) x
  letI : Module.Projective (MonoidAlgebra A I) P_S :=
    fixed_constituent_lift_projective_of_order_prime_to_p
      (A := A) (p := p) hp I hIcop
  letI : Module k[I] Sbar.toSubmodule :=
    representationCarrierGroupAlgebraModule Sbar.toRepresentation
  letI : IsScalarTower k k[I] Sbar.toSubmodule :=
    representationCarrierGroupAlgebraIsScalarTower Sbar.toRepresentation
  letI : Module A Sbar.toSubmodule := Module.compHom Sbar.toSubmodule (algebraMap A k)
  letI : IsScalarTower A k Sbar.toSubmodule :=
    moduleCompHomIsScalarTower (R := A) (S := k) (M := Sbar.toSubmodule)
  let hred : red_S.IsResidueFieldReduction I := by
    simpa using hLiftSbar
  let N : Submodule A (ρA_I.IntertwiningMap ρA_I) :=
    Submodule.span A ({Representation.IntertwiningMap.id ρA_I} :
      Set (ρA_I.IntertwiningMap ρA_I))
  let redEnd :=
    fixed_constituent_endAlgHom
      (A := A) (G := G) (V := V) (I := I) (ρ := ρ) (Sbar := Sbar)
      ρA_I red_S hLiftSbar
  have hmapRed : Submodule.map redEnd.toLinearMap N = ⊤ := by
    -- Serre's reduced Schur lemma says the reduction of the scalar line already fills
    -- `End_{k[I]}(S̄)`.
    simpa [N, redEnd] using
      fixed_constituent_scalar_line_closed_fiber_top
        (A := A) (G := G) (V := V) hp I hIcop ρ Sbar hSbar_irred
        ρA_I red_S hLiftSbar
  letI : Module k k := Semiring.toModule
  letI : Module A k := Algebra.toModule
  letI : IsScalarTower A k k := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  letI : Algebra A (Sbar.toRepresentation.IntertwiningMap Sbar.toRepresentation) :=
    reducedRepresentationEndAlgebra (R := A) Sbar.toRepresentation
  letI : IsScalarTower A k (Sbar.toRepresentation.IntertwiningMap Sbar.toRepresentation) :=
    reducedRepresentationEndScalarTower (R := A) Sbar.toRepresentation
  let ρA₀ : Representation A I P_S := Representation.ofModule' P_S
  let ρk₀ : Representation k I Sbar.toSubmodule := Representation.ofModule' Sbar.toSubmodule
  letI : Algebra A (ρk₀.IntertwiningMap ρk₀) :=
    Algebra.compHom (ρk₀.IntertwiningMap ρk₀) (algebraMap A k)
  letI : IsScalarTower A k (ρk₀.IntertwiningMap ρk₀) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ by
      ext x
      rfl
  letI :
      Algebra A
        ((Representation.ofModule' Sbar.toSubmodule :
            Representation k I Sbar.toSubmodule).IntertwiningMap
          (Representation.ofModule' Sbar.toSubmodule :
            Representation k I Sbar.toSubmodule)) :=
    Algebra.compHom
      ((Representation.ofModule' Sbar.toSubmodule :
          Representation k I Sbar.toSubmodule).IntertwiningMap
        (Representation.ofModule' Sbar.toSubmodule :
          Representation k I Sbar.toSubmodule))
      (algebraMap A k)
  letI :
      IsScalarTower A k
        ((Representation.ofModule' Sbar.toSubmodule :
            Representation k I Sbar.toSubmodule).IntertwiningMap
          (Representation.ofModule' Sbar.toSubmodule :
            Representation k I Sbar.toSubmodule)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ by
      ext x
      rfl
  let eSource : ρA_I.IntertwiningMap ρA_I ≃ₗ[A]
      ρA₀.IntertwiningMap ρA₀ :=
    (representationEquivOfModuleEndAlgEquiv ρA_I).toLinearEquiv
  let eTargetK :
      Sbar.toRepresentation.IntertwiningMap Sbar.toRepresentation ≃ₗ[k]
        ρk₀.IntertwiningMap ρk₀ :=
    (representationEquivOfModuleEndAlgEquiv Sbar.toRepresentation).toLinearEquiv
  let eTarget :
      Sbar.toRepresentation.IntertwiningMap Sbar.toRepresentation ≃ₗ[A]
        ρk₀.IntertwiningMap ρk₀ :=
    { toFun := fun x ↦ eTargetK x
      invFun := fun x ↦ eTargetK.symm x
      map_add' := by
        intro x y
        exact eTargetK.map_add x y
      map_smul' := by
        intro a x
        change eTargetK ((algebraMap A k a) • x) = (algebraMap A k a) • eTargetK x
        exact eTargetK.map_smul (algebraMap A k a) x
      left_inv := by
        intro x
        exact eTargetK.left_inv x
      right_inv := by
        intro x
        exact eTargetK.right_inv x }
  let N₀ : Submodule A (ρA₀.IntertwiningMap ρA₀) := N.map eSource.toLinearMap
  have hcomp :
      hred.endAlgHom.toLinearMap.comp eSource.toLinearMap =
        eTarget.toLinearMap.comp redEnd.toLinearMap := by
    apply LinearMap.ext
    intro x
    have hredEnd :
        redEnd x =
          (representationEquivOfModuleEndAlgEquiv Sbar.toRepresentation).symm
            (hred.endAlgHom (eSource x)) := by
      rfl
    change hred.endAlgHom (eSource x) = eTargetK (redEnd x)
    rw [hredEnd]
    simp [eTargetK]
  have hmapRed₀ : Submodule.map hred.endAlgHom.toLinearMap N₀ = ⊤ := by
    calc
      Submodule.map hred.endAlgHom.toLinearMap N₀ =
          Submodule.map (hred.endAlgHom.toLinearMap.comp eSource.toLinearMap) N := by
            simpa [N₀] using
              (Submodule.map_comp eSource.toLinearMap hred.endAlgHom.toLinearMap N).symm
      _ = Submodule.map (eTarget.toLinearMap.comp redEnd.toLinearMap) N := by
            rw [hcomp]
      _ = Submodule.map eTarget.toLinearMap (Submodule.map redEnd.toLinearMap N) := by
            simpa using Submodule.map_comp redEnd.toLinearMap eTarget.toLinearMap N
      _ = ⊤ := by
            simpa [hmapRed] using congrArg (Submodule.map eTarget.toLinearMap) hmapRed
  letI : Module.Finite A (ρA₀.IntertwiningMap ρA₀) :=
    equivariantEndomorphismAlgebra_finite (A := A) (G := I) P_S
  have hbase := LinearMap.IsResidueFieldReduction.endAlgHom_isBaseChange
    (A := A) (G := I) (f := red_S) hred
  have hmapTensor₀ :
      N₀.map (TensorProduct.mk A k (ρA₀.IntertwiningMap ρA₀) 1) = ⊤ := by
    rw [eq_top_iff]
    intro t ht
    have htImage : hbase.equiv t ∈ N₀.map hred.endAlgHom.toLinearMap := by
      simpa [hmapRed₀] using
        (show hbase.equiv t ∈
          (⊤ : Submodule A (ρk₀.IntertwiningMap ρk₀)) from
            trivial)
    rcases Submodule.mem_map.mp htImage with ⟨x, hxN, hxred⟩
    refine Submodule.mem_map.mpr ⟨x, hxN, ?_⟩
    apply hbase.equiv.injective
    calc
      hbase.equiv ((TensorProduct.mk A k (ρA₀.IntertwiningMap ρA₀) 1) x) =
          hred.endAlgHom x := by
            simpa using hbase.equiv_tmul (1 : k) x
      _ = hbase.equiv t := hxred
  have hN₀top : N₀ = ⊤ := by
    exact
      (IsLocalRing.map_tensorProduct_mk_eq_top
        (R := A) (M := ρA₀.IntertwiningMap ρA₀) (N := N₀)).1 hmapTensor₀
  have huN : u ∈ N := by
    have heu : eSource u ∈ N₀ := by
      simpa [hN₀top] using
        (show eSource u ∈ (⊤ : Submodule A (ρA₀.IntertwiningMap ρA₀)) from trivial)
    obtain ⟨v, hvN, hv⟩ : ∃ v, v ∈ N ∧ eSource v = eSource u :=
      Submodule.mem_map.mp heu
    have hvu : v = u := eSource.injective hv
    simpa [hvu] using hvN
  rcases Submodule.mem_span_singleton.mp huN with ⟨a, ha⟩
  exact ⟨a, ha.symm⟩

/-- Helper for Theorem 17-17.6-1: if an automorphism of a finite free `A`-module is a scalar
multiple of the identity map, then that scalar is automatically a unit. This is the exact linear
algebra step needed to turn a scalar classification of `End_{A[I]}(P_S)` into Serre's literal
kernel statement `U₁ = Aˣ`. -/
theorem linearEquiv_eq_unit_smul_refl_of_linearMap_eq_smul_id
    {M : Type*} [AddCommGroup M] [Module A M]
    [Module.Free A M] [Module.Finite A M]
    (e : M ≃ₗ[A] M) {a : A}
    (h : (e : M →ₗ[A] M) = a • LinearMap.id) :
    ∃ u : Aˣ, e = u • LinearEquiv.refl A M := by
  by_cases hM : Subsingleton M
  · letI : Subsingleton M := hM
    -- On the zero-rank carrier, every linear equivalence is already the identity homothety.
    refine ⟨1, ?_⟩
    ext x
    have hx : x = 0 := Subsingleton.elim _ _
    subst hx
    simp
  · have hfinpos : 0 < Module.finrank A M := by
      -- Outside the degenerate case, the free finite carrier has positive rank.
      exact
        (Module.finrank_pos_iff_of_free (R := A) (M := M)).2
          (not_subsingleton_iff_nontrivial.mp hM)
    have hdetUnit : IsUnit (LinearMap.det ((e : M →ₗ[A] M))) := by
      -- An invertible linear map has unit determinant.
      refine LinearMap.isUnit_det (e : M →ₗ[A] M) ?_
      exact
        ⟨⟨(e : M →ₗ[A] M), (e.symm : M →ₗ[A] M),
          by
            ext x
            simp,
          by
            ext x
            simp⟩, rfl⟩
    have hpowUnit : IsUnit (a ^ Module.finrank A M) := by
      -- The determinant of a scalar endomorphism is the corresponding power of that scalar.
      simpa [h, LinearMap.det_smul, LinearMap.det_id] using hdetUnit
    have haUnit : IsUnit a := by
      exact (isUnit_pow_iff (Nat.ne_of_gt hfinpos)).1 hpowUnit
    refine ⟨haUnit.unit, ?_⟩
    ext x
    have h' : (e : M →ₗ[A] M) = (haUnit.unit : A) • LinearMap.id := by
      simpa [haUnit.unit_spec] using h
    -- Re-express the equality on underlying linear maps as an equality of linear equivalences.
    change
      ((e : M →ₗ[A] M) x) =
        ((((haUnit.unit : Aˣ) • LinearEquiv.refl A M : M ≃ₗ[A] M) : M →ₗ[A] M) x)
    simp [h']

/-- Helper for Theorem 17-17.6-1: once every equivariant endomorphism of the fixed lift `ρA_I`
is scalar, Serre's literal kernel fiber `U₁` is exactly the scalar unit group `Aˣ`. This isolates
the only remaining source-faithful gap before the determinant-normalized cover construction. -/
theorem fixed_constituent_transport_kernel_eq_unit_smul_id_of_endomorphism_scalar
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (hscalar :
      ∀ f : ρA_I.IntertwiningMap ρA_I,
        ∃ a : A, f = a • Representation.IntertwiningMap.id ρA_I)
    (u :
      fixed_constituent_transport_fiber
        (A := A) (G := G) I ρA_I (1 : G)) :
    ∃ a : Aˣ, u.toLinearEquiv = a • LinearEquiv.refl A P_S := by
  obtain ⟨a, ha⟩ :=
    hscalar
      (fixed_constituent_transport_kernel_intertwiningEnd
        (A := A) (G := G) (I := I) (ρA_I := ρA_I) u)
  -- First rewrite the kernel transport as a scalar endomorphism in `End_{A[I]}(P_S)`.
  refine
    linearEquiv_eq_unit_smul_refl_of_linearMap_eq_smul_id
      (A := A) (M := P_S) u.toLinearEquiv (a := a) ?_
  change
    (fixed_constituent_transport_kernel_intertwiningEnd
      (A := A) (G := G) (I := I) (ρA_I := ρA_I) u : P_S →ₗ[A] P_S) =
      a • LinearMap.id
  simpa [fixed_constituent_transport_kernel_intertwiningEnd] using
    congrArg (fun f : ρA_I.IntertwiningMap ρA_I => (f : P_S →ₗ[A] P_S)) ha

/-- Helper for Theorem 17-17.6-1: inverting a transport operator moves from `U_s` to `U_{s⁻¹}`.
This is the literal inverse operation on Serre's total space `G₁`. -/
noncomputable def fixed_constituent_transport_fiber_inv
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    {s : G}
    (u :
      fixed_constituent_transport_fiber
        (A := A) (G := G) I ρA_I s) :
    fixed_constituent_transport_fiber
      (A := A) (G := G) I ρA_I s⁻¹ := by
  refine Representation.Equiv.mk u.symm.toLinearEquiv ?_
  intro a
  ext x
  -- Apply the original intertwining relation at the conjugated element `(s a s⁻¹)` and rewrite
  -- the source action on the nose to obtain the inverse transport law.
  have htransport0 :
      (ρA_I ((MulAut.conjNormal s) a)) (u (u.symm x)) =
        u ((ρA_I a) (u.symm x)) := by
    simpa [MulAut.conjNormal_apply, mul_assoc] using
      (LinearMap.congr_fun (u.isIntertwining' ((MulAut.conjNormal s) a)) (u.symm x)).symm
  have htransport :
      ((MonoidHom.comp ρA_I (MulEquiv.toMonoidHom (MulAut.conjNormal s⁻¹⁻¹))) a) x =
        u.toLinearEquiv ((ρA_I a ∘ₗ u.symm.toLinearEquiv) x) := by
    rw [u.apply_symm_apply] at htransport0
    simpa [LinearMap.comp_apply] using htransport0
  exact u.toLinearEquiv.symm_apply_eq.mpr htransport

/-- Helper for Theorem 17-17.6-1: Serre's literal total space `G₁ = Σ s, U_s` already carries the
transport-composition multiplication before the scalar-kernel analysis that cuts out `G₂`. -/
noncomputable def fixed_constituent_transport_total_space_mul
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S) :
    fixed_constituent_transport_total_space (A := A) (G := G) I ρA_I →
      fixed_constituent_transport_total_space (A := A) (G := G) I ρA_I →
        fixed_constituent_transport_total_space (A := A) (G := G) I ρA_I :=
  fun g h ↦
    ⟨g.1 * h.1,
      fixed_constituent_transport_fiber_comp
        (A := A) (G := G) (I := I) (ρA_I := ρA_I) g.2 h.2⟩

/-- Helper for Theorem 17-17.6-1: the chosen section of Serre's projection `G₁ → G` is a genuine
right inverse on the nose. This stabilizes the source-level surjectivity data before the later
determinant-normalized subgroup `G₂` is introduced. -/
theorem fixed_constituent_transport_total_space_proj_section
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (s : G) :
    fixed_constituent_transport_total_space_proj
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)
        (fixed_constituent_transport_total_space_section
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s) =
      s := rfl

/-- Helper for Theorem 17-17.6-1: the literal multiplication on Serre's total space `G₁`
projects to the ambient group multiplication in `G`. This isolates the first group-theoretic
compatibility needed before the determinant-normalized cover data can be packaged. -/
theorem fixed_constituent_transport_total_space_proj_mul
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (g h : fixed_constituent_transport_total_space (A := A) (G := G) I ρA_I) :
    fixed_constituent_transport_total_space_proj
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)
        (fixed_constituent_transport_total_space_mul
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) g h) =
      fixed_constituent_transport_total_space_proj
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) g *
        fixed_constituent_transport_total_space_proj
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) h := by
  rfl

/-- Helper for Theorem 17-17.6-1: the literal inverse on Serre's total space `G₁` projects to the
inverse in the ambient group `G`. This keeps the group package on `G₁` aligned with the source
projection `G₁ → G`. -/
theorem fixed_constituent_transport_total_space_proj_inv
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (g : fixed_constituent_transport_total_space (A := A) (G := G) I ρA_I) :
    fixed_constituent_transport_total_space_proj
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)
        ⟨g.1⁻¹,
          fixed_constituent_transport_fiber_inv
            (A := A) (G := G) (I := I) (ρA_I := ρA_I) g.2⟩ =
      (fixed_constituent_transport_total_space_proj
        (A := A) (G := G) (I := I) (ρA_I := ρA_I) g)⁻¹ := by
  rfl

/-- Helper for Theorem 17-17.6-1: transport operators over equal group elements are
heterogeneously equal when they agree as maps on the lifted constituent. -/
private theorem fixed_constituent_transport_fiber_heq_of_apply_eq
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    {s t : G} (hst : s = t)
    {u : fixed_constituent_transport_fiber (A := A) (G := G) I ρA_I s}
    {v : fixed_constituent_transport_fiber (A := A) (G := G) I ρA_I t}
    (h : ∀ x : P_S, u x = v x) :
    HEq u v := by
  subst t
  apply heq_of_eq
  ext x
  exact h x

/-- Helper for Theorem 17-17.6-1: Serre's literal total space `G₁ = Σ s, U_s` already carries
the obvious group law coming from fiber composition, before the determinant normalization that
cuts out the finite subgroup `G₂`. -/
private noncomputable instance fixed_constituent_transport_total_space_group
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S) :
    Group (fixed_constituent_transport_total_space (A := A) (G := G) I ρA_I) where
  mul :=
    fixed_constituent_transport_total_space_mul
      (A := A) (G := G) (I := I) (ρA_I := ρA_I)
  one :=
    ⟨1,
      fixed_constituent_transport_fiber_one
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)⟩
  inv := fun g ↦
    ⟨g.1⁻¹,
      fixed_constituent_transport_fiber_inv
        (A := A) (G := G) (I := I) (ρA_I := ρA_I) g.2⟩
  mul_assoc := by
    -- Both products act on the lifted constituent carrier by the same triple composition.
    rintro ⟨a, ua⟩ ⟨b, ub⟩ ⟨c, uc⟩
    apply Sigma.ext
    · exact mul_assoc a b c
    · refine fixed_constituent_transport_fiber_heq_of_apply_eq I ρA_I
        (mul_assoc a b c) ?_
      intro x
      rfl
  one_mul := by
    -- The neutral fiber element is the identity automorphism on the lift carrier.
    rintro ⟨a, ua⟩
    apply Sigma.ext
    · exact one_mul a
    · refine fixed_constituent_transport_fiber_heq_of_apply_eq I ρA_I
        (one_mul a) ?_
      intro x
      rfl
  mul_one := by
    -- Right multiplication by the identity fiber also acts trivially on the lift carrier.
    rintro ⟨a, ua⟩
    apply Sigma.ext
    · exact mul_one a
    · refine fixed_constituent_transport_fiber_heq_of_apply_eq I ρA_I
        (mul_one a) ?_
      intro x
      rfl
  inv_mul_cancel := by
    -- Composing a fiber element with its inverse is the identity transport in `U₁`.
    rintro ⟨a, ua⟩
    apply Sigma.ext
    · exact inv_mul_cancel a
    · refine fixed_constituent_transport_fiber_heq_of_apply_eq I ρA_I
        (inv_mul_cancel a)
        (u := fixed_constituent_transport_fiber_comp
          (A := A) (G := G) I ρA_I
          (fixed_constituent_transport_fiber_inv (A := A) (G := G) I ρA_I ua) ua)
        (v := fixed_constituent_transport_fiber_one (A := A) (G := G) I ρA_I) ?_
      intro x
      unfold fixed_constituent_transport_fiber_comp
      rw [Representation.Equiv.trans_apply]
      exact Representation.Equiv.symm_apply_apply ua x

/-- Helper for Theorem 17-17.6-1: the identity element of Serre's transport total space is the
identity group element together with the identity transport operator. -/
@[simp]
theorem fixed_constituent_transport_total_space_one
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S) :
    (1 : fixed_constituent_transport_total_space (A := A) (G := G) I ρA_I) =
      ⟨1,
        fixed_constituent_transport_fiber_one
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)⟩ := by
  rfl

/-- Helper for Theorem 17-17.6-1: multiplication in Serre's transport total space is the
fiberwise transport-composition operation. -/
@[simp]
theorem fixed_constituent_transport_total_space_mul_eq
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (g h : fixed_constituent_transport_total_space (A := A) (G := G) I ρA_I) :
    g * h =
      fixed_constituent_transport_total_space_mul
        (A := A) (G := G) (I := I) (ρA_I := ρA_I) g h := by
  rfl

/-- Helper for Theorem 17-17.6-1: the total-space projection from Serre's transport cover is a
group homomorphism. -/
noncomputable def fixed_constituent_transport_total_space_proj_hom
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S) :
    fixed_constituent_transport_total_space (A := A) (G := G) I ρA_I →* G where
  toFun :=
    fixed_constituent_transport_total_space_proj
      (A := A) (G := G) (I := I) (ρA_I := ρA_I)
  map_one' := rfl
  map_mul' g h :=
    fixed_constituent_transport_total_space_proj_mul
      (A := A) (G := G) (I := I) (ρA_I := ρA_I) g h

end

end Representation
