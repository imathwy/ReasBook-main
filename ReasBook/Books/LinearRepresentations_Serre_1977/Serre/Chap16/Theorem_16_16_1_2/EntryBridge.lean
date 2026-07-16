import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap14.Corollary_14_14_4_3.ProjectiveModules
import LinearRepresentations_Serre_1977.Serre.Chap15.Definition_15_15_2_1
import LinearRepresentations_Serre_1977.Serre.Chap15.Definition_15_15_3_1
import LinearRepresentations_Serre_1977.Serre.Chap15.Proposition_15_15_5_1.StableLatticeExactOwner
import LinearRepresentations_Serre_1977.Serre.Chap16.Theorem_16_16_1_2.HomFiber

/-!
# Brauer reciprocity entry bridge for Theorem 16-16.1-2

This support module assembles the "common-owner" `Hom`-fiber comparisons used to compute the
scalar-extension matrix entry `e` of Serre's Brauer reciprocity, identifying it with the
matching decomposition-matrix entry.  The pieces it wires together are:

* `Serre/Chap16/Theorem_16_16_1_2/HomFiber.lean`: the field-independent `Hom`-fiber dimension
  `finrank S (scalarExtIntertwiner A G Q T S) = finrank A (Q →ₗ[A[G]] T)`;
* `Serre/Chap15/Proposition_15_15_5_1/StableLatticeExactOwner.lean`: the identification of the
  ambient `K`-representation with the scalar extension of the exact lattice owner.

Everything here is faithful: it is exactly Serre's "the two Cartan-type pairings are computed by the
same `Hom` fiber over the discrete-valuation ring `A`" step.
-/

noncomputable section

open CategoryTheory
open scoped MonoidAlgebra Representation TensorProduct

universe u

namespace Representation

section IntertwiningCongr

variable {F : Type u} [Field F] {G : Type u} [Group G]

/-- Transporting an intertwining-map dimension along representation equivalences on both arguments:
if `ρ ≃ ρ'` and `σ ≃ σ'` as representations, then `Hom(ρ, σ)` and `Hom(ρ', σ')` have the same
`F`-dimension. -/
theorem IntertwiningMap.finrank_eq_of_equiv
    {V V' W W' : Type u}
    [AddCommGroup V] [Module F V] [AddCommGroup V'] [Module F V']
    [AddCommGroup W] [Module F W] [AddCommGroup W'] [Module F W']
    {ρ : Representation F G V} {ρ' : Representation F G V'}
    {σ : Representation F G W} {σ' : Representation F G W'}
    (eρ : ρ.Equiv ρ') (eσ : σ.Equiv σ') :
    Module.finrank F (Representation.IntertwiningMap ρ σ) =
      Module.finrank F (Representation.IntertwiningMap ρ' σ') := by
  classical
  -- Build an `F`-linear equivalence `Hom(ρ, σ) ≃ₗ Hom(ρ', σ')` by conjugating with the given
  -- equivalences:  `f ↦ eσ ∘ f ∘ eρ⁻¹`.
  let toFun : Representation.IntertwiningMap ρ σ → Representation.IntertwiningMap ρ' σ' :=
    fun f ↦ eσ.toIntertwiningMap.comp (f.comp eρ.symm.toIntertwiningMap)
  let invFun : Representation.IntertwiningMap ρ' σ' → Representation.IntertwiningMap ρ σ :=
    fun f ↦ eσ.symm.toIntertwiningMap.comp (f.comp eρ.toIntertwiningMap)
  have hleft : ∀ f, invFun (toFun f) = f := by
    intro f
    apply Representation.IntertwiningMap.ext
    ext v
    simp [invFun, toFun]
  have hright : ∀ f, toFun (invFun f) = f := by
    intro f
    apply Representation.IntertwiningMap.ext
    ext v
    simp [invFun, toFun]
  let e : Representation.IntertwiningMap ρ σ ≃ₗ[F] Representation.IntertwiningMap ρ' σ' :=
    { toFun := toFun
      invFun := invFun
      left_inv := hleft
      right_inv := hright
      map_add' := by
        intro f g
        apply Representation.IntertwiningMap.ext
        ext v
        simp [toFun]
      map_smul' := by
        intro a f
        apply Representation.IntertwiningMap.ext
        ext v
        simp [toFun] }
  exact e.finrank_eq

end IntertwiningCongr

section OfModulePrime

variable {F : Type u} [Field F] {G : Type u} [Group G]

/-- The identity is an equivalence between `ofModule' M` and any representation `ρ` on the same
carrier whose action is left multiplication by `MonoidAlgebra.of F G g` (i.e. matches the ambient
`F[G]`-module structure of `M`). -/
def ofModulePrimeEquivOfActionEq
    {M : Type u} [AddCommGroup M] [Module F M] [Module F[G] M] [IsScalarTower F F[G] M]
    (ρ : Representation F G M)
    (hρ : ∀ (g : G) (x : M), ρ g x = MonoidAlgebra.of F G g • x) :
    (Representation.ofModule' (k := F) (G := G) M).Equiv ρ :=
  Representation.Equiv.mk (LinearEquiv.refl F M) fun g ↦ by
    ext x
    simp only [LinearMap.comp_apply, LinearEquiv.refl_apply, LinearEquiv.coe_coe]
    rw [hρ g x]
    simp [Representation.ofModule', MonoidAlgebra.of]

end OfModulePrime

section ScalarExtensionFunctorial

variable {A : Type u} [CommRing A]
variable {F : Type u} [CommRing F] [Algebra A F]
variable {G : Type u} [Group G]

/-- Scalar extension of representations along `A → F` is functorial in equivalences: an equivalence
`ρ ≃ σ` of `A`-representations scalar-extends to an equivalence of the base-changed
`F`-representations. -/
def scalarExtensionEquiv
    {M N : Type u} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    {ρ : Representation A G M} {σ : Representation A G N}
    (e : ρ.Equiv σ) :
    (Representation.scalarExtension (k := F) ρ).Equiv
      (Representation.scalarExtension (k := F) σ) :=
  Representation.Equiv.mk (e.toLinearEquiv.baseChange A F M N) fun g ↦ by
    apply TensorProduct.AlgebraTensorModule.ext
    intro a x
    have hx := LinearMap.congr_fun (e.toIntertwiningMap.isIntertwining' g) x
    have hscalarρ : (Representation.scalarExtension (k := F) ρ) g
        = LinearMap.baseChange F (ρ g) := by
      simp [Representation.scalarExtension, Module.End.baseChangeHom, LinearMap.baseChangeHom_apply]
    have hscalarσ : (Representation.scalarExtension (k := F) σ) g
        = LinearMap.baseChange F (σ g) := by
      simp [Representation.scalarExtension, Module.End.baseChangeHom, LinearMap.baseChangeHom_apply]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    show (e.toLinearEquiv.baseChange A F M N)
        ((Representation.scalarExtension (k := F) ρ) g (a ⊗ₜ[A] x))
      = (Representation.scalarExtension (k := F) σ) g
        ((e.toLinearEquiv.baseChange A F M N) (a ⊗ₜ[A] x))
    rw [hscalarρ, hscalarσ, LinearMap.baseChange_tmul, LinearEquiv.baseChange_tmul,
      LinearEquiv.baseChange_tmul, LinearMap.baseChange_tmul]
    exact congrArg (fun y ↦ a ⊗ₜ[A] y) hx

end ScalarExtensionFunctorial

end Representation
