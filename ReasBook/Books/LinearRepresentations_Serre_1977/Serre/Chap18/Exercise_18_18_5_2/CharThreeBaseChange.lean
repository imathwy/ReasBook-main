import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_5_2.LinearCharacters
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_5_2.OrdinaryExplicitModels
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_5_2.SemisimpleEquivTransport
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_5_2.CharTwoBaseChange
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_5_2.PrimeFieldInfrastructure
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_5_2.PrimeFieldTransport
import LinearRepresentations_Serre_1977.Serre.RepresentationTheory.RealizableOver

/-!
# Base change of the sign and `sgn ⊗ std` models (support for Exercise 18.5.2)

Over an algebraically closed field `k`, this file identifies the scalar extensions (from the prime
subfield `↥(⊥ : Subfield k)`) of two of Serre's explicit prime-field `S₄`-models with their native
counterparts over `k`:

* `s4_primefield_sign_scalarExtension_equiv` — the **sign** representation, and
* `s4_primefield_sign_standard_tensor_scalarExtension_equiv` — the **`sgn ⊗ std`** representation.

The sign bridge is a one-dimensional scalar computation; the `sgn ⊗ std` bridge is obtained via the
"twist route": tensoring by a degree-`1` character is, up to equivalence, a same-carrier scalar
twist, and the twist commutes with scalar extension, reducing everything to the (characteristic-free)
base-change equivalence of the permutation-augmentation representation.
-/

-- The Fong–Swan import chain re-introduces the global `Field.henselian` instance, which makes
-- typeclass search diverge.  Removals are file-local, so re-disable it here (cf. sibling files).
attribute [-instance] Field.henselian

noncomputable section

open Representation
open scoped TensorProduct

namespace Representation

universe u v w

section

local notation "S4" => Equiv.Perm (Fin 4)

variable {k : Type u} [Field k]

-- Pin the canonical submodule structures on the degree-`3` standard augmentation carrier over the
-- prime subfield (cf. `PrimeFieldTransport.lean`); the lattice-defined carrier is otherwise slow to
-- re-synthesize and triggers the `AddCommGroup.toAddCommMonoid` vs `Submodule.addCommMonoid` diamond.
local instance :
    AddCommGroup
      ↥(permutationAugmentationSubrepresentation ↥(⊥ : Subfield k) S4 (Fin 4)).toSubmodule :=
  (permutationAugmentationSubrepresentation ↥(⊥ : Subfield k) S4 (Fin 4)).toSubmodule.addCommGroup
local instance :
    Module ↥(⊥ : Subfield k)
      ↥(permutationAugmentationSubrepresentation ↥(⊥ : Subfield k) S4 (Fin 4)).toSubmodule :=
  (permutationAugmentationSubrepresentation ↥(⊥ : Subfield k) S4 (Fin 4)).toSubmodule.module

-- Pin the scalar-extension module and tower on the standard carrier.  These synthesize fine in a
-- clean context but the imported instance soup makes the in-tactic search diverge under the default
-- `synthInstance` budget; pinning them lets us pass the tower explicitly where needed.
local instance iTM :
    Module ↥(⊥ : Subfield k)
      (k ⊗[↥(⊥ : Subfield k)]
        ↥(permutationAugmentationSubrepresentation ↥(⊥ : Subfield k) S4 (Fin 4)).toSubmodule) :=
  inferInstance
local instance iST :
    IsScalarTower ↥(⊥ : Subfield k) k
      (k ⊗[↥(⊥ : Subfield k)]
        ↥(permutationAugmentationSubrepresentation ↥(⊥ : Subfield k) S4 (Fin 4)).toSubmodule) :=
  inferInstance

/-- Restatement (definitionally true) of the action of a scalar extension as the base-change of the
acting endomorphism.  Mirrors the `private` companion in `CharTwoBaseChange.lean`. -/
private theorem scalarExt_apply {k₀ : Type*} [Field k₀] {K : Type*} [Field K] [Algebra k₀ K]
    {G : Type*} [Group G] {W : Type*} [AddCommGroup W] [Module k₀ W]
    (ρ : Representation k₀ G W) (g : G) :
    (scalarExtension (k := K) ρ) g = LinearMap.baseChange K (ρ g) := rfl

/-- The coefficient map sends the prime-field value of the `S₄`-sign character to its native value
over `k`.  Both sides are the integer cast of `Equiv.Perm.sign`. -/
private lemma s4_sign_algebraMap_eq (g : S4) :
    algebraMap ↥(⊥ : Subfield k) k
        ((s4_sign_character ↥(⊥ : Subfield k) g : ↥(⊥ : Subfield k)))
      = (s4_sign_character k g : k) := by
  have h := s4_primefield_sign_character_map (k := k) g
  simpa [s4_sign_representation, unitCharacterRepresentation_character_apply] using h

/-! ## Generic transport helpers -/

/-- Scalar extension respects equivalence of representations. -/
def scalarExtension_congr {k₀ : Type*} [Field k₀] {K : Type*} [Field K] [Algebra k₀ K]
    {G : Type*} [Group G]
    {W₀ : Type*} [AddCommGroup W₀] [Module k₀ W₀]
    {W₀' : Type*} [AddCommGroup W₀'] [Module k₀ W₀']
    {ρ₀ : Representation k₀ G W₀} {σ₀ : Representation k₀ G W₀'}
    (e : ρ₀.Equiv σ₀) :
    (scalarExtension (k := K) ρ₀).Equiv (scalarExtension (k := K) σ₀) :=
  Representation.Equiv.mk
    (LinearEquiv.ofLinear
      (LinearMap.baseChange K e.toLinearEquiv.toLinearMap)
      (LinearMap.baseChange K e.toLinearEquiv.symm.toLinearMap)
      (by
        rw [← LinearMap.baseChange_comp,
          show e.toLinearEquiv.toLinearMap.comp e.toLinearEquiv.symm.toLinearMap
              = LinearMap.id from by ext x; exact e.toLinearEquiv.apply_symm_apply x,
          LinearMap.baseChange_id])
      (by
        rw [← LinearMap.baseChange_comp,
          show e.toLinearEquiv.symm.toLinearMap.comp e.toLinearEquiv.toLinearMap
              = LinearMap.id from by ext x; exact e.toLinearEquiv.symm_apply_apply x,
          LinearMap.baseChange_id]))
    (fun g => by
      have hint : e.toLinearEquiv.toLinearMap.comp (ρ₀ g)
          = (σ₀ g).comp e.toLinearEquiv.toLinearMap := e.isIntertwining' g
      show (LinearMap.baseChange K e.toLinearEquiv.toLinearMap).comp
            (LinearMap.baseChange K (ρ₀ g))
          = (LinearMap.baseChange K (σ₀ g)).comp
            (LinearMap.baseChange K e.toLinearEquiv.toLinearMap)
      rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, hint])

/-- The same-carrier scalar twist by a unit-valued character respects equivalence. -/
def unitCharacterTwist_congr {K : Type*} [Field K] {G : Type*} [Group G]
    {W W' : Type*} [AddCommGroup W] [Module K W] [AddCommGroup W'] [Module K W']
    (β : G →* Kˣ) {ρ : Representation K G W} {σ : Representation K G W'}
    (e : ρ.Equiv σ) :
    (unitCharacterTwistRepresentation_overField β ρ).Equiv
      (unitCharacterTwistRepresentation_overField β σ) :=
  Representation.Equiv.mk e.toLinearEquiv (fun g => by
    have hint : e.toLinearEquiv.toLinearMap.comp (ρ g)
        = (σ g).comp e.toLinearEquiv.toLinearMap := e.isIntertwining' g
    show e.toLinearEquiv.toLinearMap.comp (((β g : Kˣ) : K) • ρ g)
        = (((β g : Kˣ) : K) • σ g).comp e.toLinearEquiv.toLinearMap
    rw [LinearMap.comp_smul, LinearMap.smul_comp, hint])

/-! ## The sign bridge -/

/-- The canonical right-unit tensor equivalence intertwines the scalar-extended prime-field sign
representation with the native sign representation over `k`. -/
private lemma s4_primefield_sign_scalarExtension_isIntertwining :
    ∀ g : S4,
      (Algebra.TensorProduct.rid ↥(⊥ : Subfield k) k k).toLinearEquiv.toLinearMap.comp
          ((scalarExtension (k := k) (s4_sign_representation ↥(⊥ : Subfield k))) g)
        = ((s4_sign_representation k) g).comp
            (Algebra.TensorProduct.rid ↥(⊥ : Subfield k) k k).toLinearEquiv.toLinearMap := by
  intro g
  apply LinearMap.ext
  intro t
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add p q hp hq => simp only [map_add, LinearMap.comp_apply] at hp hq ⊢; rw [hp, hq]
  | tmul a z =>
      rw [LinearMap.comp_apply, scalarExt_apply, LinearMap.baseChange_tmul, LinearMap.comp_apply]
      simp only [LinearEquiv.coe_coe, AlgEquiv.toLinearEquiv_apply, Algebra.TensorProduct.rid_tmul]
      rw [show (s4_sign_representation ↥(⊥ : Subfield k)) g
            = LinearMap.lsmul ↥(⊥ : Subfield k) ↥(⊥ : Subfield k)
                (s4_sign_character ↥(⊥ : Subfield k) g : ↥(⊥ : Subfield k)) from rfl,
          show (s4_sign_representation k) g
            = LinearMap.lsmul k k (s4_sign_character k g : k) from rfl,
          LinearMap.lsmul_apply, LinearMap.lsmul_apply, smul_eq_mul, smul_eq_mul,
          Algebra.smul_def, map_mul, s4_sign_algebraMap_eq, Algebra.smul_def, mul_assoc]

/-- **Sign bridge.**  The scalar extension to `k` of the prime-field sign representation of `S₄` is
equivalent to the native sign representation over `k`. -/
def s4_primefield_sign_scalarExtension_equiv :
    (Representation.scalarExtension (k := k) (s4_sign_representation ↥(⊥ : Subfield k))).Equiv
      (s4_sign_representation k) :=
  Representation.Equiv.mk
    (Algebra.TensorProduct.rid ↥(⊥ : Subfield k) k k).toLinearEquiv
    s4_primefield_sign_scalarExtension_isIntertwining

/-! ## The `sgn ⊗ std` bridge -/

/-- Scalar extension commutes with the sign scalar twist: the scalar extension of the prime-field
`sign`-twist of the standard model coincides with the `k`-sign-twist of the scalar-extended standard
model.  Both share the carrier `k ⊗[↥⊥] W`, and the underlying map is the identity. -/
def s4_sign_scalarExtension_twist_equiv :
    (scalarExtension (k := k)
        (unitCharacterTwistRepresentation_overField (s4_sign_character ↥(⊥ : Subfield k))
          (s4_standard_augmentation_representation ↥(⊥ : Subfield k)))).Equiv
      (unitCharacterTwistRepresentation_overField (s4_sign_character k)
        (scalarExtension (k := k) (s4_standard_augmentation_representation ↥(⊥ : Subfield k)))) := by
  -- The two representations are *equal* (same carrier, equal actions), so transport `Equiv.refl`.
  have hAB :
      (scalarExtension (k := k)
          (unitCharacterTwistRepresentation_overField (s4_sign_character ↥(⊥ : Subfield k))
            (s4_standard_augmentation_representation ↥(⊥ : Subfield k))))
        = (unitCharacterTwistRepresentation_overField (s4_sign_character k)
            (scalarExtension (k := k)
              (s4_standard_augmentation_representation ↥(⊥ : Subfield k)))) := by
    refine MonoidHom.ext (fun g => ?_)
    rw [scalarExt_apply]
    simp only [unitCharacterTwistRepresentation_overField, MonoidHom.coe_mk, OneHom.coe_mk]
    rw [LinearMap.baseChange_smul, scalarExt_apply]
    apply LinearMap.ext
    intro Y
    rw [LinearMap.smul_apply, LinearMap.smul_apply, ← s4_sign_algebraMap_eq]
    exact @algebra_compatible_smul _ _ k _ _ _ _ _ _ iST _ _
  exact hAB ▸ Representation.Equiv.refl _

/-- **`sgn ⊗ std` bridge.**  The scalar extension to `k` of the prime-field `sgn ⊗ std`
representation of `S₄` is equivalent to the native `sgn ⊗ std` representation over `k`.  The
hypothesis `h2 : (2 : k) ≠ 0` is recorded to match the call site (characteristic `3`); the proof
itself is characteristic-free. -/
theorem s4_primefield_sign_standard_tensor_scalarExtension_equiv (h2 : (2 : k) ≠ 0) :
    Nonempty ((Representation.scalarExtension (k := k)
        (s4_sign_standard_tensor_representation ↥(⊥ : Subfield k))).Equiv
      (s4_sign_standard_tensor_representation k)) := by
  classical
  obtain ⟨stdEq⟩ :=
    scalarExtension_permutationAugmentationRepresentation_equiv
      (k₀ := ↥(⊥ : Subfield k)) (k := k) (G := S4) (X := Fin 4)
  refine ⟨?_⟩
  refine
    (scalarExtension_congr (K := k)
        (unitCharacterTensorTwistEquiv_overField (s4_sign_character ↥(⊥ : Subfield k))
          (s4_standard_augmentation_representation ↥(⊥ : Subfield k)))).trans ?_
  refine s4_sign_scalarExtension_twist_equiv.trans ?_
  refine (unitCharacterTwist_congr (s4_sign_character k) stdEq).trans ?_
  exact (unitCharacterTensorTwistEquiv_overField (s4_sign_character k)
    (s4_standard_augmentation_representation k)).symm

end

end Representation
