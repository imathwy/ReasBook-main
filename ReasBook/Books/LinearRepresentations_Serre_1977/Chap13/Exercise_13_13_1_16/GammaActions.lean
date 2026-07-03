import Mathlib
import LinearRepresentations_Serre_1977.GroupTheory.ConjClassesPower

open CategoryTheory
open IsCyclotomicExtension.Rat
open scoped MonoidAlgebra Representation
open Representation

noncomputable section

universe u w

variable {G : Type u} [Group G] [Finite G]

namespace Representation

section MinimalGammaApi

variable {G : Type u} [Group G]

/-- Helper for Exercise 13-13.1-16: the natural-number representative attached to an exponent
unit in `(ℤ / exp(G)ℤ)ˣ`. -/
abbrev galoisPowerExponentUnit (t : (ZMod (Monoid.exponent G))ˣ) : ℕ :=
  (t : ZMod (Monoid.exponent G)).val

end MinimalGammaApi

section MinimalCyclotomicAction

variable {L : Type u} [Field L] [Algebra ℚ L]
variable {n : ℕ} [NeZero n] [IsCyclotomicExtension {n} ℚ L]

/-- Helper for Exercise 13-13.1-16: the canonical cyclotomic Galois action of `(ℤ / nℤ)ˣ` on an
`n`-th cyclotomic field. -/
instance cyclotomicUnitMulSemiringAction : MulSemiringAction (ZMod n)ˣ L :=
  MulSemiringAction.compHom L
    ((IsCyclotomicExtension.autEquivPow L
      (Polynomial.cyclotomic.irreducible_rat (NeZero.pos n))).symm.toMonoidHom)

end MinimalCyclotomicAction

section MinimalGammaSubgroup

variable {L : Type u} [Field L] [NumberField L]

/-- Helper for Exercise 13-13.1-16: LinearRepresentations_Serre_1977's subgroup `Γ_K ⊆ (ℤ / nℤ)ˣ` attached to an
intermediate field inside a cyclotomic realization. -/
abbrev gammaSubgroup (n : ℕ) [NeZero n] [IsCyclotomicExtension {n} ℚ L]
    (K : IntermediateField ℚ L) : Subgroup (ZMod n)ˣ :=
  (galEquivZMod n L).mapSubgroup K.fixingSubgroup

end MinimalGammaSubgroup

section MinimalGammaNotation

variable (G : Type u) [Group G] [Finite G]
variable {L : Type u} [Field L] [NumberField L]
variable [IsCyclotomicExtension {Monoid.exponent G} ℚ L]

scoped[Representation] notation:max "Γ[" K "](" G ")" =>
  gammaSubgroup (Monoid.exponent G) K

scoped[Representation] notation:max "Γ_ℚ(" G ")" =>
  (ZMod (Monoid.exponent G))ˣ

end MinimalGammaNotation

section MinimalGammaPowerAction

variable {G : Type u} [Group G] [NeZero (Monoid.exponent G)]

/-- Helper for Exercise 13-13.1-16: the ambient rational power action of exponent units on `G`. -/
instance galoisPowerPow : Pow G (ZMod (Monoid.exponent G))ˣ where
  pow s t := s ^ galoisPowerExponentUnit t

/-- Helper for Exercise 13-13.1-16: rewriting the ambient rational power action in terms of the
chosen natural-number representative. -/
@[simp] theorem pow_unit_eq_pow_nat (s : G) (t : (ZMod (Monoid.exponent G))ˣ) :
    (s ^ t : G) = s ^ galoisPowerExponentUnit t := rfl

variable {ΓK : Subgroup (ZMod (Monoid.exponent G))ˣ}

/-- Helper for Exercise 13-13.1-16: LinearRepresentations_Serre_1977's subgroup power action on `G`. -/
instance gammaSubgroupPow : Pow G ΓK where
  pow s t := s ^ galoisPowerExponentUnit (t : (ZMod (Monoid.exponent G))ˣ)

/-- Helper for Exercise 13-13.1-16: rewriting the subgroup rational power action in terms of the
underlying exponent unit. -/
@[simp] theorem pow_subgroup_eq_pow_nat (s : G) (t : ΓK) :
    (s ^ t : G) = s ^ galoisPowerExponentUnit (t : (ZMod (Monoid.exponent G))ˣ) := rfl

end MinimalGammaPowerAction

end Representation

/-- The unit element of `Γ_ℚ` acts trivially on conjugacy classes. -/
theorem one_smul_conjClasses (c : ConjClasses G) :
    ConjClasses.pow (galoisPowerExponentUnit (1 : Γ_ℚ(G))) c = c :=
  by
    obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective c
    apply congrArg ConjClasses.mk
    have hmod :
        galoisPowerExponentUnit (1 : Γ_ℚ(G)) ≡ 1 [MOD Monoid.exponent G] := by
      rw [← ZMod.natCast_eq_natCast_iff]
      simp [galoisPowerExponentUnit]
    calc
      g ^ galoisPowerExponentUnit (1 : Γ_ℚ(G)) = g ^ 1 := by
        exact pow_eq_pow_of_modEq hmod (Monoid.pow_exponent_eq_one g)
      _ = g := pow_one g

/-- The powering maps on conjugacy classes compose according to multiplication in `Γ_ℚ`. -/
theorem mul_smul_conjClasses (t u : Γ_ℚ(G)) (c : ConjClasses G) :
    ConjClasses.pow (galoisPowerExponentUnit (t * u)) c =
      ConjClasses.pow (galoisPowerExponentUnit t)
        (ConjClasses.pow (galoisPowerExponentUnit u) c) :=
  by
    obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective c
    apply congrArg ConjClasses.mk
    have hmod :
        galoisPowerExponentUnit (t * u) ≡
          galoisPowerExponentUnit u * galoisPowerExponentUnit t [MOD Monoid.exponent G] := by
      rw [Nat.mul_comm]
      rw [← ZMod.natCast_eq_natCast_iff]
      simp [galoisPowerExponentUnit, Nat.cast_mul]
    calc
      g ^ galoisPowerExponentUnit (t * u)
          = g ^ (galoisPowerExponentUnit u * galoisPowerExponentUnit t) := by
            exact pow_eq_pow_of_modEq hmod (Monoid.pow_exponent_eq_one g)
      _ = (g ^ galoisPowerExponentUnit u) ^ galoisPowerExponentUnit t := by
            rw [pow_mul]

/-- The canonical `Γ_ℚ`-action on conjugacy classes, given by `x ↦ x^t`. -/
instance gammaRatMulActionConjClasses :
    MulAction (Γ_ℚ(G)) (ConjClasses G) where
  smul t c := ConjClasses.pow (galoisPowerExponentUnit t) c
  one_smul := one_smul_conjClasses
  mul_smul := mul_smul_conjClasses

section CyclotomicHomAction

variable {K : Type u} [Field K] [NumberField K]
variable [IsCyclotomicExtension {Monoid.exponent G} ℚ K]
variable {A : Type w} [Semiring A] [Algebra ℚ A]

/-- Postcomposition by the cyclotomic Galois automorphism attached to `t ∈ Γ_ℚ`. -/
def smulCyclotomicAlgHom (t : Γ_ℚ(G)) (φ : A →ₐ[ℚ] K) :
    A →ₐ[ℚ] K :=
  ((galEquivZMod (Monoid.exponent G) K).symm t).toAlgHom.comp φ

/-- The identity element of `Γ_ℚ` acts trivially on `ℚ`-algebra homomorphisms into `K`. -/
theorem one_smul_cyclotomicAlgHom (φ : A →ₐ[ℚ] K) :
    smulCyclotomicAlgHom (1 : Γ_ℚ(G)) φ = φ := by
  have hσ :
      (galEquivZMod (Monoid.exponent G) K).symm (1 : Γ_ℚ(G)) = 1 :=
    (galEquivZMod (Monoid.exponent G) K).symm.map_one
  ext a
  simp [smulCyclotomicAlgHom, hσ]

/-- The cyclotomic Galois action on algebra homomorphisms is compatible with multiplication in
`Γ_ℚ`. -/
theorem mul_smul_cyclotomicAlgHom (t u : Γ_ℚ(G)) (φ : A →ₐ[ℚ] K) :
    smulCyclotomicAlgHom (t * u) φ =
      smulCyclotomicAlgHom t (smulCyclotomicAlgHom u φ) := by
  have hσ :
      (galEquivZMod (Monoid.exponent G) K).symm (t * u) =
        (galEquivZMod (Monoid.exponent G) K).symm t *
          (galEquivZMod (Monoid.exponent G) K).symm u := by
    exact (galEquivZMod (Monoid.exponent G) K).symm.map_mul t u
  ext a
  simp [smulCyclotomicAlgHom, hσ, AlgHom.comp_apply]

/-- The canonical `Γ_ℚ`-action on `ℚ`-algebra homomorphisms into the cyclotomic field `K`. -/
instance gammaRatMulActionAlgHom :
    MulAction (Γ_ℚ(G)) (A →ₐ[ℚ] K) where
  smul := smulCyclotomicAlgHom
  one_smul := one_smul_cyclotomicAlgHom
  mul_smul := mul_smul_cyclotomicAlgHom

/-- Helper for Exercise 13-13.1-16: precomposition with a `ℚ`-algebra equivalence transports the
cyclotomic `Γ_ℚ`-action on `K`-valued points equivariantly. -/
theorem algHom_action_isomorphic_of_algEquiv
    {B : Type w} [Semiring B] [Algebra ℚ B]
    (e : A ≃ₐ[ℚ] B) :
    IsIsomorphic
      (Action.ofMulAction (Γ_ℚ(G)) (A →ₐ[ℚ] K))
      (Action.ofMulAction (Γ_ℚ(G)) (B →ₐ[ℚ] K)) := by
  let eAlgHom : (A →ₐ[ℚ] K) ≃ (B →ₐ[ℚ] K) :=
    { toFun := fun φ ↦ φ.comp e.symm.toAlgHom
      invFun := fun ψ ↦ ψ.comp e.toAlgHom
      left_inv := by
        intro φ
        ext a
        simp
      right_inv := by
        intro ψ
        ext b
        simp }
  refine ⟨Action.mkIso eAlgHom.toIso ?_⟩
  intro t
  rfl

end CyclotomicHomAction
