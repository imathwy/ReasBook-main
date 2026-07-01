import Mathlib
import Serre.Chap02.Proposition_2_2_2_1
import Serre.Chap03.Theorem_3_3_2_1
import Serre.Chap06.Corollary_6_6_5_4
import Serre.Chap06.Proposition_6_6_5_5
import Serre.Chap12.Exercise_12_12_2_3.API
import Serre.Chap12.Exercise_12_12_2_6.ExternalTensorUniverseBridge
import Serre.Chap12.Exercise_12_12_2_6.FieldDenominatorPrelude
import Serre.Chap12.Proposition_12_12_2_1

noncomputable section

open scoped BigOperators
open scoped Representation
open scoped Representation.ExternalTensor

universe u v w

namespace Representation

open CategoryTheory
open Exercise_12_12_2_6

section FieldPart

variable {K : Type u} [Field K] [CharZero K]
variable {G : Type u} [Group G] [Finite G]

local instance instFintypeGExercise_12_12_2_6_field_tensor : Fintype G := Fintype.ofFinite G

/-- Helper for Exercise 12-12.2-6: quotienting by a normal subgroup acting trivially preserves
irreducibility over any field. -/
theorem ofQuotient_preserves_irreducibility_local
    {L : Type w} [Field L]
    {V : Type*} [AddCommGroup V] [Module L V]
    (σ : Representation L G V) (S : Subgroup G) [S.Normal]
    [Representation.IsTrivial (σ.comp S.subtype)] [σ.IsIrreducible] :
    Representation.IsIrreducible (σ.ofQuotient S) := by
  classical
  letI : Nontrivial (Subrepresentation (σ.ofQuotient S)) := by
    refine ⟨⟨⊥, ⊤, ?_⟩⟩
    intro h
    have h' : (⊥ : Subrepresentation σ) = ⊤ := by
      apply Subrepresentation.toSubmodule_injective
      simpa using congrArg Subrepresentation.toSubmodule h
    exact IsSimpleOrder.bot_ne_top h'
  refine IsSimpleOrder.of_forall_eq_top ?_
  intro W hW
  let W' : Subrepresentation σ :=
    { toSubmodule := W.toSubmodule
      apply_mem_toSubmodule := by
        intro g x hx
        simpa using W.apply_mem_toSubmodule (g : G ⧸ S) hx }
  have hW'_ne_bot : W' ≠ ⊥ := by
    intro hW'
    apply hW
    apply Subrepresentation.toSubmodule_injective
    simpa [W'] using congrArg Subrepresentation.toSubmodule hW'
  have hW'_top : W' = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top W').resolve_left hW'_ne_bot
  apply Subrepresentation.toSubmodule_injective
  simpa [W'] using congrArg Subrepresentation.toSubmodule hW'_top

/-- Helper for Exercise 12-12.2-6: the `n`-fold tensor-power representation over an arbitrary
field acts coordinatewise on the `n`-fold tensor power. -/
def tensorPowerRep_field_local
    {L : Type w} [Field L]
    {V : Type*} [AddCommGroup V] [Module L V]
    (ρ : Representation L G V) (n : ℕ) :
    Representation L (Fin n → G) (TensorPower L n V) where
  toFun g := PiTensorProduct.map (fun i ↦ ρ (g i))
  map_one' := by
    -- Coordinatewise identity maps induce the identity on the full tensor product.
    simpa using (PiTensorProduct.map_one (R := L) (s := fun _ : Fin n ↦ V))
  map_mul' g h := by
    -- Coordinatewise multiplication transports through `PiTensorProduct.map`.
    simpa using
      (PiTensorProduct.map_mul (R := L) (s := fun _ : Fin n ↦ V)
        (f₁ := fun i ↦ ρ (g i)) (f₂ := fun i ↦ ρ (h i)))

/-- Helper for Exercise 12-12.2-6: the one-fold tensor power is the original representation after
identifying `Fin 1 → G` with `G`. -/
noncomputable def tensorPowerRepOneEquiv_field_local
    {L : Type w} [Field L]
    {V : Type*} [AddCommGroup V] [Module L V]
    (ρ : Representation L G V) :
    (tensorPowerRep_field_local (G := G) ρ 1).Equiv
      (ρ.comp finOneMulEquiv.toMonoidHom) :=
  Representation.Equiv.mk
    (PiTensorProduct.subsingletonEquiv (R := L) (s := fun _ : Fin 1 ↦ V) 0)
    (fun g ↦ by
      -- On pure tensors, the singleton tensor-product action is the original action.
      ext f
      simp [tensorPowerRep_field_local, finOneMulEquiv,
        PiTensorProduct.subsingletonEquiv_apply_tprod])

/-- Helper for Exercise 12-12.2-6: splitting a tuple into its first `n` coordinates and final
coordinate and then appending them again recovers the original tuple. -/
theorem fin_append_castAdd_last_field_local
    {α : Type*} (n : ℕ) (f : Fin (n + 1) → α) :
    Fin.append (fun i : Fin n ↦ f (Fin.castAdd 1 i)) (fun _ : Fin 1 ↦ f (Fin.last n)) = f := by
  -- This is the exact `Fin.append` reconstruction used when splitting off the last tensor factor.
  have hlast : Fin.natAdd n (0 : Fin 1) = Fin.last n := by
    simpa using (Fin.natAdd_last (n := n) (m := 0))
  calc
    Fin.append (fun i : Fin n ↦ f (Fin.castAdd 1 i)) (fun _ : Fin 1 ↦ f (Fin.last n))
        =
          Fin.append (fun i : Fin n ↦ f (Fin.castAdd 1 i))
            (fun i : Fin 1 ↦ f (Fin.natAdd n i)) := by
              congr 1
              funext i
              fin_cases i
              simpa using congrArg f hlast.symm
    _ = f := Fin.append_castAdd_natAdd (f := f)

/-- Helper for Exercise 12-12.2-6: the inverse of `TensorPower.mulEquiv` on a pure tensor splits
off the last tensor coordinate. -/
theorem tensorPower_mulEquiv_symm_tprod_split_last_field_local
    {L : Type w} [Field L]
    {V : Type*} [AddCommGroup V] [Module L V]
    (n : ℕ) (f : Fin (n + 1) → V) :
    (TensorPower.mulEquiv (R := L) (M := V) (n := n) (m := 1)).symm
      (PiTensorProduct.tprod L f)
      =
        (PiTensorProduct.tprod L (fun i : Fin n ↦ f (Fin.castAdd 1 i))) ⊗ₜ[L]
          (PiTensorProduct.tprod L (fun i : Fin 1 ↦ f (Fin.natAdd n i))) := by
  -- Apply the forward equivalence so the goal becomes the standard tensor multiplication rule.
  apply (TensorPower.mulEquiv (R := L) (M := V) (n := n) (m := 1)).injective
  calc
    TensorPower.mulEquiv (R := L) (M := V) (n := n) (m := 1)
        ((TensorPower.mulEquiv (R := L) (M := V) (n := n) (m := 1)).symm
          (PiTensorProduct.tprod L f))
        = PiTensorProduct.tprod L f := by
            rw [LinearEquiv.apply_symm_apply]
    _ =
        PiTensorProduct.tprod L
          (Fin.append (fun i : Fin n ↦ f (Fin.castAdd 1 i)) (fun i : Fin 1 ↦ f (Fin.natAdd n i))) := by
            congr 1
            exact (Fin.append_castAdd_natAdd (f := f)).symm
    _ =
        TensorPower.mulEquiv (R := L) (M := V) (n := n) (m := 1)
          ((PiTensorProduct.tprod L (fun i : Fin n ↦ f (Fin.castAdd 1 i))) ⊗ₜ[L]
            (PiTensorProduct.tprod L (fun i : Fin 1 ↦ f (Fin.natAdd n i)))) := by
              symm
              simpa [TensorPower.gMul_def] using
                (TensorPower.tprod_mul_tprod (R := L)
                  (fun i : Fin n ↦ f (Fin.castAdd 1 i))
                  (fun i : Fin 1 ↦ f (Fin.natAdd n i)))

/-- Helper for Exercise 12-12.2-6: after splitting off the last tensor factor, the successor
tensor-power action matches the split external tensor action. -/
theorem tensorPowerRepSucc_apply_tprod_field_local
    {L : Type w} [Field L]
    {V : Type*} [AddCommGroup V] [Module L V]
    (ρ : Representation L G V) (n : ℕ)
    (g : Fin (n + 1) → G) (f : Fin (n + 1) → V) :
    let τsplit :
        Representation L ((Fin n → G) × (Fin 1 → G))
          (TensorProduct L (TensorPower L n V) (TensorPower L 1 V)) :=
      (tensorPowerRep_field_local (G := G) ρ n) ⊠
        (tensorPowerRep_field_local (G := G) ρ 1)
    TensorPower.mulEquiv (R := L) (M := V) (n := n) (m := 1)
      (((τsplit.comp (finAppendMulEquiv n 1).toMonoidHom) g)
        ((TensorPower.mulEquiv (R := L) (M := V) (n := n) (m := 1)).symm
          (PiTensorProduct.tprod L f)))
      = PiTensorProduct.tprod L (fun i ↦ ρ (g i) (f i)) := by
  -- Route correction: first isolate the `mulEquiv.symm` reindexing, then evaluate the split
  -- external tensor action.
  dsimp
  rw [tensorPower_mulEquiv_symm_tprod_split_last_field_local (L := L) (V := V)]
  let f₁ : Fin n → V := fun i ↦ f (Fin.castAdd 1 i)
  let f₂ : Fin 1 → V := fun i ↦ f (Fin.natAdd n i)
  let gf₁ : Fin n → V := fun i ↦ ρ (g (Fin.castAdd 1 i)) (f (Fin.castAdd 1 i))
  let gf₂ : Fin 1 → V := fun i ↦ ρ (g (Fin.natAdd n i)) (f (Fin.natAdd n i))
  let τsplit :
      Representation L ((Fin n → G) × (Fin 1 → G))
        (TensorProduct L (TensorPower L n V) (TensorPower L 1 V)) :=
    (tensorPowerRep_field_local (G := G) ρ n) ⊠
      (tensorPowerRep_field_local (G := G) ρ 1)
  have hsplit :
      (((τsplit.comp (finAppendMulEquiv n 1).toMonoidHom) g)
        ((PiTensorProduct.tprod L f₁) ⊗ₜ[L] (PiTensorProduct.tprod L f₂)))
      =
        (PiTensorProduct.tprod L gf₁) ⊗ₜ[L] (PiTensorProduct.tprod L gf₂) := by
    simp [τsplit, f₁, f₂, gf₁, gf₂, Representation.tprod, tensorPowerRep_field_local,
      finAppendMulEquiv]
  have hsplit' :
      TensorPower.mulEquiv (R := L) (M := V) (n := n) (m := 1)
        (((τsplit.comp (finAppendMulEquiv n 1).toMonoidHom) g)
          ((PiTensorProduct.tprod L f₁) ⊗ₜ[L] (PiTensorProduct.tprod L f₂)))
      =
        TensorPower.mulEquiv (R := L) (M := V) (n := n) (m := 1)
          ((PiTensorProduct.tprod L gf₁) ⊗ₜ[L] (PiTensorProduct.tprod L gf₂)) := by
    exact congrArg (TensorPower.mulEquiv (R := L) (M := V) (n := n) (m := 1)) hsplit
  -- Recombine the two pure tensors using the tensor-power multiplication rule.
  calc
    TensorPower.mulEquiv (R := L) (M := V) (n := n) (m := 1)
        (((τsplit.comp (finAppendMulEquiv n 1).toMonoidHom) g)
          ((PiTensorProduct.tprod L f₁) ⊗ₜ[L] (PiTensorProduct.tprod L f₂)))
        = TensorPower.mulEquiv (R := L) (M := V) (n := n) (m := 1)
            ((PiTensorProduct.tprod L gf₁) ⊗ₜ[L] (PiTensorProduct.tprod L gf₂)) := hsplit'
    _ =
        TensorPower.mulEquiv (R := L) (M := V) (n := n) (m := 1)
          ((PiTensorProduct.tprod L gf₁) ⊗ₜ[L] (PiTensorProduct.tprod L gf₂)) := rfl
    _ =
        PiTensorProduct.tprod L (Fin.append gf₁ gf₂) := by
              simpa [TensorPower.gMul_def] using
                (TensorPower.tprod_mul_tprod (R := L) gf₁ gf₂)
    _ = PiTensorProduct.tprod L (fun i ↦ ρ (g i) (f i)) := by
          congr 1
          simpa [f₁, f₂, gf₁, gf₂] using
            (Fin.append_castAdd_natAdd (f := fun i : Fin (n + 1) ↦ ρ (g i) (f i)))

/-- Helper for Exercise 12-12.2-6: after splitting off the last tensor factor, the successor
tensor power is equivalent to the external tensor of the shorter power and the one-fold power. -/
noncomputable def tensorPowerRepSuccEquiv_field_local
    {L : Type w} [Field L]
    {V : Type*} [AddCommGroup V] [Module L V]
    (ρ : Representation L G V) (n : ℕ) :
    (tensorPowerRep_field_local (G := G) ρ (n + 1)).Equiv
      (((tensorPowerRep_field_local (G := G) ρ n) ⊠
          (tensorPowerRep_field_local (G := G) ρ 1)).comp
        (finAppendMulEquiv n 1).toMonoidHom) :=
  Representation.Equiv.mk
    (TensorPower.mulEquiv (R := L) (M := V) (n := n) (m := 1)).symm
    (fun g ↦ by
      -- The two actions agree on pure tensors after the standard split-recombine rewrite.
      ext f
      apply (TensorPower.mulEquiv (R := L) (M := V) (n := n) (m := 1)).injective
      simpa [eq_comm, tensorPowerRep_field_local, PiTensorProduct.map_tprod] using
        tensorPowerRepSucc_apply_tprod_field_local (G := G) (L := L) (V := V) (ρ := ρ)
          (n := n) g f)

/-- Helper for Exercise 12-12.2-6: the degree of the positive tensor power is the corresponding
power of the original degree. -/
theorem tensor_power_finrank_field_local
    {L : Type w} [Field L]
    {V : Type*} [AddCommGroup V] [Module L V]
    [FiniteDimensional L V]
    (n : ℕ) :
    Module.finrank L (TensorPower L (n + 1) V) = Module.finrank L V ^ (n + 1) := by
  induction n with
  | zero =>
      -- A one-fold tensor product is the original space.
      rw [pow_one]
      exact (PiTensorProduct.subsingletonEquiv (R := L) (s := fun _ : Fin 1 ↦ V) 0).finrank_eq
  | succ n ih =>
      -- Split off the last factor and use multiplicativity of finite dimension.
      calc
        Module.finrank L (TensorPower L ((n + 1) + 1) V)
            = Module.finrank L (TensorProduct L (TensorPower L (n + 1) V) (TensorPower L 1 V)) := by
                simpa [Nat.add_comm] using
                  (TensorPower.mulEquiv (R := L) (M := V) (n := n + 1) (m := 1)).symm.finrank_eq
        _ = Module.finrank L (TensorPower L (n + 1) V) * Module.finrank L (TensorPower L 1 V) := by
              simpa using
                (Module.finrank_tensorProduct (R := L) (S := L)
                  (M := TensorPower L (n + 1) V) (M' := TensorPower L 1 V))
        _ = Module.finrank L V ^ (n + 1) * Module.finrank L V := by
              rw [ih]
              rw [(PiTensorProduct.subsingletonEquiv (R := L) (s := fun _ : Fin 1 ↦ V) 0).finrank_eq]
        _ = Module.finrank L V ^ ((n + 1) + 1) := by
              simp [pow_succ', mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Exercise 12-12.2-6: a central tuple acts on the tensor power by the product of the
corresponding scalar character values. -/
theorem tensorPowerRep_center_tuple_action_field_local
    {L : Type w} [Field L]
    {V : Type*} [AddCommGroup V] [Module L V]
    (ρ : Representation L G V)
    (μ : Subgroup.center G →* L)
    (hμ : ∀ s : Subgroup.center G, ρ (s : G) = μ s • (1 : Module.End L V))
    (n : ℕ) (z : Fin (n + 1) → Subgroup.center G) :
    tensorPowerRep_field_local (G := G) ρ (n + 1) (centerTupleEmbedding n z) =
      (∏ i, μ (z i)) • (1 : Module.End L (TensorPower L (n + 1) V)) := by
  -- On pure tensors, each central coordinate contributes its scalar and multilinearity collects
  -- them.
  ext f
  have haction :
      PiTensorProduct.tprod L (fun i : Fin (n + 1) ↦ μ (z i) • f i) =
        (∏ i, μ (z i)) • PiTensorProduct.tprod L f := by
    exact
      (PiTensorProduct.tprod L :
        MultilinearMap L (fun _ : Fin (n + 1) ↦ V) (TensorPower L (n + 1) V)).map_smul_univ
          (fun i ↦ μ (z i)) f
  calc
    tensorPowerRep_field_local (G := G) ρ (n + 1) (centerTupleEmbedding n z)
        (PiTensorProduct.tprod L f)
        = PiTensorProduct.tprod L (fun i ↦ ρ ((z i : Subgroup.center G) : G) (f i)) := by
            simp [tensorPowerRep_field_local, centerTupleEmbedding]
    _ = PiTensorProduct.tprod L (fun i ↦ μ (z i) • f i) := by
          congr 1
          funext i
          simpa [hμ (z i)]
    _ = (∏ i, μ (z i)) • PiTensorProduct.tprod L f := haction

/-- Helper for Exercise 12-12.2-6: the product-one central subgroup acts trivially on the
positive tensor-power representation over any field. -/
theorem tensor_power_rep_product_one_center_is_trivial_field_local
    {L : Type w} [Field L]
    {V : Type*} [AddCommGroup V] [Module L V]
    (ρ : Representation L G V)
    (μ : Subgroup.center G →* L)
    (hμ : ∀ s : Subgroup.center G, ρ (s : G) = μ s • (1 : Module.End L V))
    (n : ℕ) :
    Representation.IsTrivial
      ((tensorPowerRep_field_local (G := G) ρ (n + 1)).comp (productOneCenterSubgroup n).subtype) := by
  refine ⟨?_⟩
  intro g
  rcases g.2 with ⟨z, hz, hz'⟩
  have hg : (g : Fin (n + 1) → G) = centerTupleEmbedding n z := hz'.symm
  have hprod : ∏ i, μ (z i) = 1 := by
    simpa [centerTupleProd] using congrArg μ hz
  -- Route correction: first convert the action into the scalar product from the previous helper.
  calc
    ((tensorPowerRep_field_local (G := G) ρ (n + 1)).comp (productOneCenterSubgroup n).subtype) g
        = tensorPowerRep_field_local (G := G) ρ (n + 1) (centerTupleEmbedding n z) := by
            simpa [hg]
    _ = (∏ i, μ (z i)) • (1 : Module.End L (TensorPower L (n + 1) V)) :=
          tensorPowerRep_center_tuple_action_field_local (G := G) (L := L) (V := V)
            (ρ := ρ) (μ := μ) hμ n z
    _ = LinearMap.id := by
          rw [hprod, one_smul]
          rfl

/-- Helper for Exercise 12-12.2-6: precomposing with a group equivalence preserves irreducibility
over any field. -/
theorem isIrreducible_comp_of_mulEquiv_field_local
    {L : Type w} [Field L]
    {H : Type*} [Group H]
    {V : Type*} [AddCommGroup V] [Module L V]
    (e : G ≃* H)
    (σ : Representation L H V)
    [σ.IsIrreducible] :
    Representation.IsIrreducible (σ.comp e.toMonoidHom) := by
  classical
  letI : Nontrivial (Subrepresentation (σ.comp e.toMonoidHom)) := by
    refine ⟨⟨⊥, ⊤, ?_⟩⟩
    intro h
    have h' : (⊥ : Subrepresentation σ) = ⊤ := by
      apply Subrepresentation.toSubmodule_injective
      simpa using congrArg Subrepresentation.toSubmodule h
    exact IsSimpleOrder.bot_ne_top h'
  -- The invariant subspaces for `σ` and for `σ.comp e` are the same underlying submodules.
  refine IsSimpleOrder.of_forall_eq_top ?_
  intro W hW
  let W' : Subrepresentation σ :=
    { toSubmodule := W.toSubmodule
      apply_mem_toSubmodule := by
        intro h x hx
        simpa using W.apply_mem_toSubmodule (e.symm h) hx }
  have hW'_ne_bot : W' ≠ ⊥ := by
    intro hW'
    apply hW
    apply Subrepresentation.toSubmodule_injective
    simpa [W'] using congrArg Subrepresentation.toSubmodule hW'
  have hW'_top : W' = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top W').resolve_left hW'_ne_bot
  apply Subrepresentation.toSubmodule_injective
  simpa [W'] using congrArg Subrepresentation.toSubmodule hW'_top

/-- Helper for Exercise 12-12.2-6: over an algebraically closed field, the external tensor
product of two irreducible finite-dimensional representations is irreducible. -/
def ulift_carrier_representation_max_local
    {F : Type w} [Field F]
    {G0 : Type*} [Group G0]
    {W : Type*} [AddCommGroup W] [Module F W]
    (ρ : Representation F G0 W) :
    Representation F G0 (ULift.{max u w} W) where
  toFun g :=
    { toFun := fun x ↦ ⟨ρ g x.down⟩
      map_add' := by
        intro x y
        ext
        simp
      map_smul' := by
        intro a x
        ext
        simp }
  map_one' := by
    ext x
    simp
  map_mul' g h := by
    ext x
    simp [map_mul]

/-- Helper for Exercise 12-12.2-6: lifting only the carrier into the common ambient universe
preserves irreducibility. -/
theorem isIrreducible_ulift_carrier_representation_max_local
    {F : Type w} [Field F]
    {G0 : Type*} [Group G0]
    {W : Type*} [AddCommGroup W] [Module F W]
    (ρ : Representation F G0 W)
    [ρ.IsIrreducible] :
    (ulift_carrier_representation_max_local ρ).IsIrreducible := by
  -- The lifted carrier is equivariantly identical to the original carrier.
  exact isIrreducible_of_nonempty_equiv
    ⟨Representation.Equiv.mk ULift.moduleEquiv.symm fun g => by
      ext x
      rfl⟩

/-- Helper for Exercise 12-12.2-6: lifting both the group and the carrier puts the representation
into the common universe required by the bundled Chapter 3 tensor-product theorem. -/
def ulift_group_carrier_representation_max_local
    {F : Type w} [Field F]
    {G0 : Type*} [Group G0]
    {W : Type*} [AddCommGroup W] [Module F W]
    (ρ : Representation F G0 W) :
    Representation F (ULift.{max u w} G0) (ULift.{max u w} W) :=
  ulift_carrier_representation_max_local
    (ρ := ρ.comp (MulEquiv.ulift.toMonoidHom))

/-- Helper for Exercise 12-12.2-6: the external tensor of the lifted carriers is equivariantly
the same as the original external tensor. -/
noncomputable def externalTensor_ulift_equiv_local
    {L : Type w} [Field L]
    {H : Type*} [Group H]
    {V : Type*} [AddCommGroup V] [Module L V]
    {W : Type*} [AddCommGroup W] [Module L W]
    (σ : Representation L G V) (τ : Representation L H W) :
    ((ulift_carrier_representation_max_local σ) ⊠
        (ulift_carrier_representation_max_local τ)).Equiv
      (σ ⊠ τ) :=
  Representation.Equiv.mk
    (TensorProduct.congr ULift.moduleEquiv ULift.moduleEquiv)
    (fun g => by
      ext x y
      rfl)

/-- Helper for Exercise 12-12.2-6: lifting both group coordinates and then pulling back along the
product `ULift` equivalence does not change the external tensor representation. -/
noncomputable def externalTensor_group_ulift_equiv_local
    {L : Type w} [Field L]
    {H : Type*} [Group H] [Finite H]
    {V : Type*} [AddCommGroup V] [Module L V]
    {W : Type*} [AddCommGroup W] [Module L W]
    (σ : Representation L G V) (τ : Representation L H W) :
    Representation.Equiv
      (((σ.comp (MulEquiv.ulift.toMonoidHom)) ⊠ (τ.comp (MulEquiv.ulift.toMonoidHom))).comp
        ((MulEquiv.prodCongr (MulEquiv.ulift : ULift.{max u w} G ≃* G)
          (MulEquiv.ulift : ULift.{max u w} H ≃* H)).symm.toMonoidHom))
      (σ ⊠ τ) :=
  Representation.Equiv.mk (LinearEquiv.refl L (TensorProduct L V W)) fun g => by
    -- The product-group `ULift` coordinates reduce definitionally to the original pair `(g.1,g.2)`.
    ext x y
    rfl

/-- Helper for Exercise 12-12.2-6: irreducibility survives lifting the two group variables to a
common `ULift` product and pulling back along the product equivalence. -/
theorem isIrreducible_externalTensor_group_ulift_iff_local
    {L : Type w} [Field L]
    {H : Type*} [Group H] [Finite H]
    {V : Type*} [AddCommGroup V] [Module L V]
    {W : Type*} [AddCommGroup W] [Module L W]
    (σ : Representation L G V) (τ : Representation L H W) :
    Representation.IsIrreducible (σ ⊠ τ) ↔
      Representation.IsIrreducible
        ((σ.comp (MulEquiv.ulift.toMonoidHom)) ⊠ (τ.comp (MulEquiv.ulift.toMonoidHom))) := by
  let eprod :=
    MulEquiv.prodCongr (MulEquiv.ulift : ULift G ≃* G)
      (MulEquiv.ulift : ULift H ≃* H)
  let π :
      Representation L (ULift G × ULift H) (TensorProduct L V W) :=
    ((σ.comp (MulEquiv.ulift.toMonoidHom)) ⊠ (τ.comp (MulEquiv.ulift.toMonoidHom)))
  constructor
  · intro hστ
    change Representation.IsIrreducible π
    have hpull :
        Representation.IsIrreducible (π.comp eprod.symm.toMonoidHom) := by
      -- The closed equivalence `externalTensor_group_ulift_equiv_local` identifies the pulled-back
      -- lifted tensor with the original external tensor over `G × H`.
      exact
        isIrreducible_of_nonempty_equiv
          (ρ := σ ⊠ τ)
          (σ := π.comp eprod.symm.toMonoidHom)
          ⟨(externalTensor_group_ulift_equiv_local (σ := σ) (τ := τ)).symm⟩
    letI : Representation.IsIrreducible (π.comp eprod.symm.toMonoidHom) := hpull
    have hcancel :
        Representation.IsIrreducible
          ((π.comp eprod.symm.toMonoidHom).comp eprod.toMonoidHom) := by
      -- Precomposing again with the inverse product equivalence returns to the lifted tensor.
      exact
        isIrreducible_comp_of_mulEquiv_field_local
          (G := ULift G × ULift H)
          (e := eprod)
          (σ := π.comp eprod.symm.toMonoidHom)
    letI :
        Representation.IsIrreducible
          ((π.comp eprod.symm.toMonoidHom).comp eprod.toMonoidHom) := hcancel
    have hcancel_equiv :
        Representation.Equiv
          ((π.comp eprod.symm.toMonoidHom).comp eprod.toMonoidHom) π :=
      Representation.Equiv.mk (LinearEquiv.refl L _) fun g => by
        ext z
        rfl
    -- Replace the definitional double pullback by the explicit cancel equivalence.
    exact
      isIrreducible_of_nonempty_equiv
        (ρ := ((π.comp eprod.symm.toMonoidHom).comp eprod.toMonoidHom))
        (σ := π)
        ⟨hcancel_equiv⟩
  · intro hπ
    change Representation.IsIrreducible π at hπ
    letI : Representation.IsIrreducible π := hπ
    have hpull :
        Representation.IsIrreducible (π.comp eprod.symm.toMonoidHom) := by
      -- Precomposition with the product `ULift` equivalence preserves irreducibility in the
      -- reverse direction as well.
      exact
        isIrreducible_comp_of_mulEquiv_field_local
          (G := G × H)
          (e := eprod.symm)
          (σ := π)
    letI : Representation.IsIrreducible (π.comp eprod.symm.toMonoidHom) := hpull
    -- The same explicit equivalence transports the pulled-back lifted tensor back to `σ ⊠ τ`.
    exact
      isIrreducible_of_nonempty_equiv
        (ρ := π.comp eprod.symm.toMonoidHom)
        (σ := σ ⊠ τ)
        ⟨externalTensor_group_ulift_equiv_local (σ := σ) (τ := τ)⟩

/-- Helper for Exercise 12-12.2-6: algebraic closedness is invariant under the coefficient
`ULift`, so the Chapter 3 tensor theorem applies to the same-universe owners. -/
instance ulift_isAlgClosed_local
    {L : Type w} [Field L] [IsAlgClosed L] :
    IsAlgClosed (ULift.{max u w} L) where
  splits p := by
    let e : ULift.{max u w} L ≃+* L := ULift.ringEquiv
    have hs : (Polynomial.map e.toRingHom p).Splits := IsAlgClosed.splits (Polynomial.map e.toRingHom p)
    simpa [Polynomial.map_map] using hs.map e.symm.toRingHom

/-- Helper for Exercise 12-12.2-6: the pointwise coefficient `ULift` model of a finite coordinate
space is linearly equivalent to the carrier `ULift` of the original coordinate space. -/
noncomputable def fin_ulift_fun_equiv_local
    {L : Type w} [Field L] [CharZero L]
    (n : ℕ) :
    (Fin n → ULift.{max u w} L) ≃ₗ[ULift.{max u w} L]
      ULift.{max u w} (Fin n → L) where
  toFun f := ⟨fun i ↦ (f i).down⟩
  invFun f i := ⟨f.down i⟩
  left_inv := by
    intro f
    ext i
    rfl
  right_inv := by
    intro f
    cases f
    rfl
  map_add' := by
    intro f g
    ext i
    rfl
  map_smul' := by
    intro a f
    ext i
    rfl

end FieldPart

end Representation
