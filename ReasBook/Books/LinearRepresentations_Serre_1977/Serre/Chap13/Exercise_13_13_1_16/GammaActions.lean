import Mathlib
import LinearRepresentations_Serre_1977.GroupTheory.ConjClassesPower
import LinearRepresentations_Serre_1977.Serre.Chap12.Theorem_12_12_4_1.GaloisPowerAction
import LinearRepresentations_Serre_1977.Serre.Chap12.Theorem_12_12_4_1.GammaSubgroupAction

open CategoryTheory
open IsCyclotomicExtension.Rat
open scoped MonoidAlgebra Representation
open Representation

noncomputable section

universe u w

variable {G : Type u} [Group G] [Finite G]

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
