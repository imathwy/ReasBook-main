import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.LinearAlgebra.TensorPower.Symmetric

noncomputable section

universe u v w x

namespace SymmetricPower

open PiTensorProduct
open scoped TensorProduct

section Map

variable {k : Type} [CommSemiring k]
variable {V : Type v} {W : Type w} {U : Type x}
variable [AddCommMonoid V] [Module k V]
variable [AddCommMonoid W] [Module k W]
variable [AddCommMonoid U] [Module k U]

/-- Applying the same linear map in every tensor factor respects the permutation relation
defining symmetric tensor powers. -/
private theorem rel_map (n : ℕ) (f : V →ₗ[k] W) {x y : ⨂[k] (_ : Fin n), V}
    (h : addConGen (SymmetricPower.Rel k (Fin n) V) x y) :
    addConGen (SymmetricPower.Rel k (Fin n) W)
      (PiTensorProduct.map (fun _ : Fin n ↦ f) x)
      (PiTensorProduct.map (fun _ : Fin n ↦ f) y) := by
  -- Transport the generated congruence along the tensor-power map one constructor at a time.
  induction h with
  | of x y h =>
      cases h with
      | perm e g =>
          -- On generators, mapping a pure tensor preserves the same permutation pattern.
          simpa only [PiTensorProduct.map_tprod] using
            (AddConGen.Rel.of _ _
              (SymmetricPower.Rel.perm (R := k) (ι := Fin n) e
                (fun i ↦ f (g i))))
  | refl =>
      exact AddCon.refl _ _
  | symm h ih =>
      exact AddCon.symm _ ih
  | trans h₁ h₂ ih₁ ih₂ =>
      exact AddCon.trans _ ih₁ ih₂
  | add h₁ h₂ ih₁ ih₂ =>
      -- The additive step follows from the linearity of `PiTensorProduct.map`.
      simpa [LinearMap.map_add] using
        AddCon.add (addConGen (SymmetricPower.Rel k (Fin n) W)) ih₁ ih₂

/-- The function induced on the `n`th symmetric tensor power by a linear map. -/
private def mapFun (n : ℕ) (f : V →ₗ[k] W) :
    SymmetricPower k (Fin n) V → SymmetricPower k (Fin n) W :=
  Quotient.map (PiTensorProduct.map (fun _ : Fin n ↦ f))
    (fun _ _ h ↦ rel_map n f h)

/-- The induced function on symmetric powers is additive. -/
private theorem mapFun_add (n : ℕ) (f : V →ₗ[k] W)
    (x y : SymmetricPower k (Fin n) V) :
    mapFun n f (x + y) = mapFun n f x + mapFun n f y := by
  -- Reduce the quotient statement to representatives and use additivity upstairs.
  refine AddCon.induction_on₂ x y ?_
  intro x y
  change (AddCon.mk' (addConGen (SymmetricPower.Rel k (Fin n) W)))
      (PiTensorProduct.map (fun _ : Fin n ↦ f) (x + y)) =
    (AddCon.mk' (addConGen (SymmetricPower.Rel k (Fin n) W)))
      (PiTensorProduct.map (fun _ : Fin n ↦ f) x
        + PiTensorProduct.map (fun _ : Fin n ↦ f) y)
  exact congrArg (AddCon.mk' (addConGen (SymmetricPower.Rel k (Fin n) W)))
    ((PiTensorProduct.map (fun _ : Fin n ↦ f)).map_add x y)

/-- The induced function on symmetric powers is `k`-linear. -/
private theorem mapFun_smul (n : ℕ) (f : V →ₗ[k] W) (a : k)
    (x : SymmetricPower k (Fin n) V) :
    mapFun n f (a • x) = a • mapFun n f x := by
  -- Reduce the scalar action to representatives and use linearity upstairs.
  refine AddCon.induction_on x ?_
  intro x
  change (AddCon.mk' (addConGen (SymmetricPower.Rel k (Fin n) W)))
      (PiTensorProduct.map (fun _ : Fin n ↦ f) (a • x)) =
    (AddCon.mk' (addConGen (SymmetricPower.Rel k (Fin n) W)))
      (a • PiTensorProduct.map (fun _ : Fin n ↦ f) x)
  exact congrArg (AddCon.mk' (addConGen (SymmetricPower.Rel k (Fin n) W)))
    ((PiTensorProduct.map (fun _ : Fin n ↦ f)).map_smul a x)

/-- The linear map induced on the `n`th symmetric tensor power by a linear map on the base
space. -/
def map (n : ℕ) (f : V →ₗ[k] W) :
    SymmetricPower k (Fin n) V →ₗ[k] SymmetricPower k (Fin n) W where
  toFun := mapFun n f
  map_add' := mapFun_add n f
  map_smul' := mapFun_smul n f

/- Symmetric: the functorial map on the `n`th symmetric tensor power is the linear map
`SymmetricPower.map`. -/
#check SymmetricPower.map

/-- The induced map on symmetric powers sends the identity to the identity. -/
@[simp] theorem map_id (n : ℕ) :
    map n (LinearMap.id : V →ₗ[k] V) = LinearMap.id := by
  -- Compare both linear maps on quotient representatives and invoke `PiTensorProduct.map_id`.
  ext x
  refine AddCon.induction_on x ?_
  intro x
  change (AddCon.mk' (addConGen (SymmetricPower.Rel k (Fin n) V)))
      (PiTensorProduct.map (fun _ : Fin n ↦ (LinearMap.id : V →ₗ[k] V)) x) =
    (AddCon.mk' (addConGen (SymmetricPower.Rel k (Fin n) V))) x
  exact congrArg (AddCon.mk' (addConGen (SymmetricPower.Rel k (Fin n) V)))
    (LinearMap.congr_fun
      (PiTensorProduct.map_id (R := k) (ι := Fin n) (s := fun _ ↦ V)) x)

/-- The induced map on symmetric powers is compatible with composition. -/
theorem map_comp (n : ℕ) (f : V →ₗ[k] W) (g : W →ₗ[k] U) :
    map n (g.comp f) = (map n g).comp (map n f) := by
  -- Compare both sides on quotient representatives and reduce to tensor-power functoriality.
  ext x
  refine AddCon.induction_on x ?_
  intro x
  change (AddCon.mk' (addConGen (SymmetricPower.Rel k (Fin n) U)))
      (PiTensorProduct.map (fun _ : Fin n ↦ g.comp f) x) =
    (AddCon.mk' (addConGen (SymmetricPower.Rel k (Fin n) U)))
      (((PiTensorProduct.map (fun _ : Fin n ↦ g))
          ∘ₗ (PiTensorProduct.map (fun _ : Fin n ↦ f))) x)
  exact congrArg (AddCon.mk' (addConGen (SymmetricPower.Rel k (Fin n) U)))
    (LinearMap.congr_fun
      (PiTensorProduct.map_comp
        (R := k) (ι := Fin n) (g := fun _ : Fin n ↦ g) (f := fun _ : Fin n ↦ f)) x)

end Map

section FiniteDimensional

variable {K : Type u} [Field K]
variable {ι : Type u} [Finite ι]
variable {V : Type v} [AddCommGroup V] [Module K V]

/-- Finite-dimensionality passes from a vector space to its symmetric tensor powers over a finite
index type. -/
instance [FiniteDimensional K V] : FiniteDimensional K (_root_.SymmetricPower K ι V) := by
  classical
  let b : Module.Basis (Fin (Module.finrank K V)) K V := Module.finBasis K V
  let bt :
      Module.Basis (ι → Fin (Module.finrank K V)) K (PiTensorProduct K fun _ : ι ↦ V) :=
    Basis.piTensorProduct fun _ ↦ b
  letI : FiniteDimensional K (PiTensorProduct K fun _ : ι ↦ V) :=
    Module.Basis.finiteDimensional_of_finite bt
  exact FiniteDimensional.of_surjective (mk K ι V) AddCon.mk'_surjective

end FiniteDimensional

end SymmetricPower
