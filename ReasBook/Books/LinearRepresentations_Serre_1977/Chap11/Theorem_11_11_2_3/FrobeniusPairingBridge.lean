import Mathlib
import Serre.Chap12.Proposition_12_12_1_1

noncomputable section

open scoped BigOperators Representation

universe u v w w' uK

namespace Representation

section FrobeniusPairing

open Representation Rep

variable {H : Type u} [Group H]
variable {G : Type v} [Group G]
variable [Finite H] [Finite G]

local instance frobeniusPairingBridge_fintype_H : Fintype H := Fintype.ofFinite H
local instance frobeniusPairingBridge_fintype_G : Fintype G := Fintype.ofFinite G

/-- Helper for Theorem 11-11.2-3: the tensor-level Frobenius map respects the defining
coinvariant relation for induction. -/
private theorem frobenius_tensor_relation_local
    {K : Type uK} [Field K]
    {V : Type w} [AddCommGroup V] [Module K V]
    {W : Type w'} [AddCommGroup W] [Module K W]
    (α : H →* G) (E : Representation K G V) (θ : Representation K H W)
    (f : θ.IntertwiningMap (E.comp α)) (g : H) (x : G) (y : W) :
    (((((Finsupp.lift (W →ₗ[K] V) K G) fun h ↦ E h⁻¹ ∘ₗ f.toLinearMap) ∘ₗ
          (Representation.leftRegular K G) (α g)).compl₂
        (θ g) ∘ₗ Finsupp.lsingle x)
      (1 : K))
    y =
    ((((Finsupp.lift (W →ₗ[K] V) K G) fun h ↦ E h⁻¹ ∘ₗ f.toLinearMap) ∘ₗ
        Finsupp.lsingle x)
      (1 : K)) y := by
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.compl₂_apply,
    Finsupp.lsingle_apply, Representation.ofMulAction_single, smul_eq_mul,
    Finsupp.lift_apply, map_mul, mul_inv_rev, zero_smul, Finsupp.sum_single_index, one_smul,
    IntertwiningMap.toLinearMap_apply, Module.End.mul_apply]
  have hg := LinearMap.congr_fun (f.2 g) y
  simp only [LinearMap.comp_apply] at hg
  change (E x⁻¹) ((E (α g)⁻¹) (f.toLinearMap ((θ g) y))) = (E x⁻¹) (f.toLinearMap y)
  rw [hg]
  simp

/-- Helper for Theorem 11-11.2-3: Frobenius reciprocity identifies the intertwining spaces
`Ind_α θ ⟶ E` and `θ ⟶ Res_α E` by a linear equivalence. -/
private def frobenius_intertwining_equiv_local
    {K : Type uK} [Field K]
    {V : Type w} [AddCommGroup V] [Module K V]
    {W : Type w'} [AddCommGroup W] [Module K W]
    (α : H →* G) (E : Representation K G V) (θ : Representation K H W) :
    ((ind α θ).IntertwiningMap E) ≃ₗ[K] θ.IntertwiningMap (E.comp α) where
  toFun f :=
    { toLinearMap := f.toLinearMap ∘ₗ IndV.mk α θ 1
      isIntertwining' := fun g => by
        ext x
        have hf := LinearMap.congr_fun (f.2 (α g)) (IndV.mk α θ 1 x)
        simpa [← Representation.Coinvariants.mk_inv_tmul] using hf }
  invFun f :=
    { toLinearMap := Representation.Coinvariants.lift _
        (TensorProduct.lift <| Finsupp.lift _ _ _ fun h ↦ E h⁻¹ ∘ₗ f.toLinearMap)
        (fun g => by
          simp only [Representation.tprod_apply, MonoidHom.coe_comp, Function.comp_apply,
            TensorProduct.lift_comp_map]
          congr 1
          ext x y
          exact frobenius_tensor_relation_local α E θ f g x y)
      isIntertwining' := fun g => by
        ext x
        simp }
  left_inv f := by
    ext h a
    have hf := LinearMap.congr_fun (f.2 h⁻¹) (IndV.mk α θ 1 a)
    simpa using hf.symm
  right_inv f := by
    ext x
    simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Helper for Theorem 11-11.2-3: Frobenius reciprocity for characters identifies the pairing of
`θ.character` with `(E.comp α).character` on `H` with the pairing of `(ind α θ).character` with
`E.character` on `G`. -/
theorem groupFunctionPairing_character_comp_eq_character_ind_local
    {K : Type uK} [Field K] [Invertible (Nat.card H : K)] [Invertible (Nat.card G : K)]
    {V : Type w} [AddCommGroup V] [Module K V]
    {W : Type w'} [AddCommGroup W] [Module K W]
    [FiniteDimensional K V] [FiniteDimensional K W]
    (α : H →* G) (E : Representation K G V)
    (θ : Representation K H W) :
    ⟪θ.character, Representation.character (E.comp α)⟫ =
      ⟪(ind α θ).character, E.character⟫ := by
  letI : FiniteDimensional K (G →₀ K) := by
    infer_instance
  letI : FiniteDimensional K (TensorProduct K (G →₀ K) W) := by
    infer_instance
  letI : FiniteDimensional K (IndV α θ) :=
    FiniteDimensional.of_surjective (Representation.Coinvariants.mk _)
      (Representation.Coinvariants.mk_surjective _)
  calc
    ⟪θ.character, Representation.character (E.comp α)⟫ =
        Module.finrank K (θ.IntertwiningMap (E.comp α)) := by
          simpa using
            (Representation.groupFunctionPairingOverField_character_eq_finrank_intertwiningMap K θ
              (E.comp α))
    _ = Module.finrank K ((ind α θ).IntertwiningMap E) := by
          have hdim : Module.finrank K (θ.IntertwiningMap (E.comp α)) =
              Module.finrank K ((ind α θ).IntertwiningMap E) :=
            (frobenius_intertwining_equiv_local α E θ).symm.finrank_eq
          simpa [hdim]
    _ = ⟪(ind α θ).character, E.character⟫ := by
          symm
          simpa using
            (Representation.groupFunctionPairingOverField_character_eq_finrank_intertwiningMap K
              (ind α θ) E)

end FrobeniusPairing

end Representation
